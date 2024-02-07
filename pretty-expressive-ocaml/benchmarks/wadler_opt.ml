open Pretty_expressive
open Benchtool

let {page_width; computation_width; size; _} = setup ~page_width:5 ~size:0 "wadler-opt"

let () =
  if not (size = 0) then
    raise (Arg.Bad "Size must be zero")

let cf = Printer.default_cost_factory
    ~page_width:page_width
    ~computation_width:computation_width ()

module P = Printer.MakeCompat (val cf)
open P

let doc =
  group (text "AAA" <> nl) <>
  nest 5
    (group (text "B" <> nl <>
            text "B" <> nl <>
            text "B"))

let () = print_string (pretty_print doc)
