open Core_bench

module Command = Core.Command

let print_layout oc (s: string): unit =
  Printf.fprintf oc "%s\n" s

let param_out = ref None
let param_view_lines = ref false
let param_iter = ref 0
let param_size = ref 0

type config = { size: int; page_limit: int; com_limit: int }

let setup ?(size = 0) ?(width = 80) ?(limit = 100) (): config =
  let param_width = ref width in
  let param_limit = ref limit in
  param_size := size;
  let main_command =
    Command.basic
      ~summary: "Run a benchmark"
      (let%map_open.Command width =
         flag
           "--width"
           (optional_with_default width int)
           ~doc: (Printf.sprintf "int Page width limit (default: %d)" width)
       and limit =
         flag
           "--limit"
           (optional_with_default limit int)
           ~doc: (Printf.sprintf "int Computation width limit (default: %d)" limit)
       and iter =
         flag
           "--iter"
           (optional_with_default 0 int)
           ~doc: ("int Number of iterations\n" ^
                  "(default: 0; 0 uses core bench's default value)")
       and size =
         flag
           "--size"
           (optional_with_default size int)
           ~doc: (Printf.sprintf "int Size (default: %d)" size)
       and out =
         flag
           "--out"
           (optional string)
           ~doc: ("path Output the actual layout to a specified path;\n" ^
                  "- means stdout (default: do not output)")

       and view_lines =
         flag
           "--view-lines"
           no_arg
           ~doc: " Output the number of lines (default: no)"

       and view_cost =
         flag
           "--view-cost"
           no_arg
           ~doc: " Output cost (default: no)"

       and memo_limit =
         flag
           "--memo-limit"
           (optional_with_default !Printer.param_memo_limit int)
           ~doc: "int Memoization limit (default: 7)"

       in
       fun () ->
         Sys_unix.override_argv [| Sys.argv.(0) |];
         param_view_lines := view_lines;
         param_out := out;
         param_iter := iter;
         Printer.param_memo_limit := memo_limit;
         Printer.param_view_cost := view_cost;
         param_width := width;
         param_limit := limit;
         param_size := size)
  in
  Command_unix.run main_command;
  { page_limit = !param_width;
    com_limit = !param_limit;
    size = !param_size }

let instrument f () =
  let out = f () in
  begin
    match !param_out with
    | None -> ()
    | Some path ->
      begin
        if path = "-" then print_layout stdout out
        else
          let oc = open_out path in
          print_layout oc out;
          close_out oc
      end;
      Stdlib.flush_all ()
  end;
  if !param_view_lines then begin
    Printf.printf "(lines %d)\n"
      (1 + (Core.String.count out ~f:(fun x -> x = '\n')));
    Stdlib.flush_all ()
  end

let measure_time f =
  let f = instrument (fun () -> f !param_size) in
  Bench.bench
    ~run_config:
      (Bench.Run_config.create
         ?quota:
           (if !param_iter = 0 then None
            else Some (Bench.Quota.Num_calls !param_iter))
         ())
    [Bench.Test.create ~name:"Benchmark" f];
