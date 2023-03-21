open Pretty.Printer
open Benchtool

let {page_width; computation_width; size; _} = setup ~size:1000 "flatten"

module P = Printer (DefaultCost (struct
                      let page_width = page_width
                      let computation_width = computation_width
                    end))

open P

let rec quadratic (n : int): doc =
  if n = 0 then text "line"
  else group (quadratic (n - 1)) <> nl <> text "line"

let doc = quadratic size

let () = do_bench (fun () -> print doc)
