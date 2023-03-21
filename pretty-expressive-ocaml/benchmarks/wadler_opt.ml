open Pretty.Printer
open Benchtool

let {page_width; computation_width; size; _} = setup ~page_width:5 ~size:0 "wadler-opt"

let () =
  if not (size = 0) then
    raise (Arg.Bad "Size must be zero")

module P = Printer (DefaultCost (struct
                      let page_width = page_width
                      let computation_width = computation_width
                    end))

open P

let doc =
  group (text "AAA" <> nl) <>
  nest 5
    (group (text "B" <> nl <>
            text "B" <> nl <>
            text "B"))

let () = print_string (pretty_print doc)
