open Printer
open Benchtool

let {page_limit; com_limit; size; _} = setup ~width:5 ~size:0 ()

let () =
  if not (size = 0) then
    raise (Arg.Bad "bad size")

module P = Printer (DefaultCost (struct
                      let limit = com_limit
                      let width_limit = page_limit
                    end))

open P

let doc =
  group (text "AAA" <> nl) <>
  nest 5
    (group (text "B" <> nl <>
            text "B" <> nl <>
            text "B"))

let () = print_string (render doc)
