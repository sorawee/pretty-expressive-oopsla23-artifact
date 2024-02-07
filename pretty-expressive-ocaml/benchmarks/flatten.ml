open Pretty_expressive
open Benchtool

let {page_width; computation_width; size; _} = setup ~size:1000 "flatten"

let cf = Printer.default_cost_factory
    ~page_width:page_width
    ~computation_width:computation_width ()

module P = Printer.MakeCompat (val cf)
open P

let rec quadratic (n : int): doc =
  if n = 0 then text "line"
  else group (quadratic (n - 1)) <> nl <> text "line"

let doc = quadratic size

let () = do_bench (fun () -> print doc)
