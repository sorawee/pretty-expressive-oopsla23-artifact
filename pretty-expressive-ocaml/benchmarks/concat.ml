open Pretty_expressive
open Benchtool

let {page_width; computation_width; size; _} = setup ~size:10000 "concat"

let cf = Printer.default_cost_factory
    ~page_width:page_width
    ~computation_width:computation_width ()

module P = Printer.MakeCompat (val cf)
open P

let rec pp (n : int): doc =
  if n = 0 then empty
  else (pp (n - 1)) <> text "line"

let doc = pp size

let () = do_bench (fun () -> print doc)
