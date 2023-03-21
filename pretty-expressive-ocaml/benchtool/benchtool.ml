module Command = Core.Command

open Pretty
open Printer

let print_layout oc (s: string): unit =
  Printf.fprintf oc "%s\n" s

let param_out = ref None
let param_iter = ref 0
let param_size = ref 0
let param_page_width = ref 0
let param_computation_width = ref 0
let param_program = ref ""
let param_view_cost = ref false

type config = { size: int; page_width: int; computation_width: int }

let setup ?(size = 0) ?(page_width = 80) ?(computation_width = 100) (program: string): config =
  param_size := size;
  param_page_width := page_width;
  param_computation_width := computation_width;
  param_program := program;
  let main_command =
    Command.basic
      ~summary: "Run a benchmark"
      (let%map_open.Command page_width =
         flag
           "--page-width"
           (optional_with_default page_width int)
           ~doc: (Printf.sprintf "int Page width limit (default: %d)" page_width)
       and computation_width =
         flag
           "--computation-width"
           (optional_with_default computation_width int)
           ~doc: (Printf.sprintf "int Computation width limit (default: %d)" computation_width)
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

       and view_cost =
         flag
           "--view-cost"
           no_arg
           ~doc: " Output cost (default: no)"

       and memo_limit =
         flag
           "--memo-limit"
           (optional_with_default !param_memo_limit int)
           ~doc: "int Memoization limit (default: 7)"

       in
       fun () ->
         Sys_unix.override_argv [| Sys.argv.(0) |];
         param_memo_limit := memo_limit;
         param_out := out;
         param_view_cost := view_cost;
         param_page_width := page_width;
         param_computation_width := computation_width;
         param_size := size)
  in
  Command_unix.run main_command;
  { page_width = !param_page_width;
    computation_width = !param_computation_width;
    size = !param_size }

let do_bench (f : unit -> Info.info) =
  let at_init = Sys.time () in
  let out_info = f () in
  let at_end = Sys.time () in
  let out = out_info.out in
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
  begin
    if !param_view_cost then
      Printf.printf "(cost %s)\n" out_info.cost
  end;
  let module S = Core.Sexp in
  Printf.printf "%s\n"
    (S.to_string
       (S.List
          [S.List
             [S.Atom "target";
              S.Atom "pretty-expressive-ocaml"];

           S.List
             [S.Atom "program";
              S.Atom !param_program];

           S.List
             [S.Atom "duration";
              S.Atom (string_of_float (at_end -. at_init))];

           S.List
             [S.Atom "lines";
              S.Atom (string_of_int
                        (1 + (Core.String.count out ~f:(fun x -> x = '\n'))))];

           S.List
             [S.Atom "size";
              S.Atom (string_of_int !param_size)];

           S.List
             [S.Atom "md5";
              S.Atom (out |> Digest.string |> Digest.to_hex)];

           S.List
             [S.Atom "page-width";
              S.Atom (string_of_int !param_page_width)];

           S.List
             [S.Atom "computation-width";
              S.Atom (string_of_int !param_computation_width)];

           S.List
             [S.Atom "tainted?";
              S.Atom (if out_info.is_tainted then "true" else "false")];

           S.List
             [S.Atom "memo-limit";
              S.Atom (string_of_int !param_memo_limit)]]))

(* Core bench unfortunately doesn't meet the flexibility that I want. *)

(* Bench.bench *)
(*   ~display_config: *)
(*     (Bench.Display_config.create *)
(*        ~show_output_as_sexp: true *)
(*        ()) *)
(*     ~run_config: *)
(*       (Bench.Run_config.create *)
(*          ?quota: *)
(*            (if !param_iter = 0 then None *)
(*             else Some (Bench.Quota.Num_calls !param_iter)) *)
(*          ()) *)
(*     [Bench.Test.create ~name:"Benchmark" f]; *)
