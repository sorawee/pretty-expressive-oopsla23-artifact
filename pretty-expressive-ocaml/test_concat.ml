open Printer
open Test_lib

let {page_limit; com_limit; _} = setup ~size:10000 ()

module P = Printer (Cost (struct
                      let limit = com_limit
                      let width_limit = page_limit
                    end))

open P

let rec pp (n : int): doc =
  if n = 0 then text ""
  else (pp (n - 1)) <> text "line"

let () = measure_time (fun size -> render (pp size))
