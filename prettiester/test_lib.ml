open Core_bench

module Command = Core.Command

let print_layout (s: string): unit =
  print_string s;
  print_string "\n"

let param_view_layout = ref false
let param_view_lines = ref false
let param_iter = ref 0
let param_series = ref false
let param_size = ref 0

let setup ?(size = 0) ?(width = 80) ?(limit = 100) (): int * int =
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
           ~doc: ("int Document size\n" ^
                  (Printf.sprintf
                     "(default: %d; 0 as a default value implies unused)"
                     size))
       and view_layout =
         flag
           "--view-layout"
           no_arg
           ~doc: " Output the actual layout (default: no)"

       and view_lines =
         flag
           "--view-lines"
           no_arg
           ~doc: " Output the number of lines (default: no)"

       and view_memo =
         flag
           "--view-memo"
           no_arg
           ~doc: " Output memoization stats (default: no)"

       and view_cost =
         flag
           "--view-cost"
           no_arg
           ~doc: " Output cost (default: no)"

       and series =
         flag
           "--series"
           no_arg
           ~doc: " Runs from s = 1 .. size (default: no)"

       and memo_limit =
         flag
           "--memo-limit"
           (optional_with_default !Printer.param_memo_limit int)
           ~doc: "int Memoization limit (default: 7)"

       in
       fun () ->
         Sys_unix.override_argv [| Sys.argv.(0) |];
         param_view_lines := view_lines;
         param_view_layout := view_layout;
         param_iter := iter;
         param_series := series;
         Printer.param_memo_limit := memo_limit;
         Printer.param_view_memo := view_memo;
         Printer.param_view_cost := view_cost;
         param_width := width;
         param_limit := limit;
         param_size := size)
  in
  Command_unix.run main_command;
  (!param_width, !param_limit)

let cnt_runs = ref 0

let instrument f () =
  cnt_runs := !cnt_runs + 1;
  let out = f () in
  if !param_view_layout then print_layout out;
  if !param_view_lines then
    Printf.printf "(lines %d)\n"
      (1 + (Core.String.count out ~f:(fun x -> x = '\n')));
  Stdlib.flush_all ()

let measure_time_int f =
  let f = instrument f in
  Bench.bench
    ~run_config:
      (Bench.Run_config.create
         ?quota:
           (if !param_iter = 0 then None
            else Some (Bench.Quota.Num_calls !param_iter))
         ())
    [Bench.Test.create ~name:"Benchmark" f];
  Printf.printf "(total-run %d)\n" !cnt_runs;
  cnt_runs := 0

let measure_time f =
  if !param_series then
    for i = 1 to !param_size do
      Printf.printf "(size %d)\n" i;
      measure_time_int (fun () -> f i)
    done
  else
    measure_time_int (fun () -> f !param_size)
