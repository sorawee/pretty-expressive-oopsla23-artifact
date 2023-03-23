open Printer
open Test_lib

let (page_limit, com_limit) = setup ~width:5 ()

module P = Printer (Cost (struct
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

let () = print_layout (render doc)
