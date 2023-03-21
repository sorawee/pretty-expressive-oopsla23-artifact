open Pretty.Printer
open Benchtool

let {page_width; computation_width; size; _} = setup ~size:10000 "concat"

module P = Printer (DefaultCost (struct
                      let page_width = page_width
                      let computation_width = computation_width
                    end))

open P

let rec pp (n : int): doc =
  if n = 0 then empty
  else (pp (n - 1)) <> text "line"

let doc = pp size

let () = do_bench (fun () -> print doc)
