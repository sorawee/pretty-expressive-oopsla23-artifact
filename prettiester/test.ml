open Printer

module P = Printer (Cost (struct
                      let limit = 10
                      let width_limit = 10
                    end))

open P

let a = text "aaaa"

let s = render (a <> (nl <|> nl))
let () =
  Printf.printf "%s\n" s
