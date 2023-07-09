open Printer
open Benchtool

let {page_limit; com_limit; _} = setup ~size:1000 ()

module P = Printer (DefaultCost (struct
                      let limit = com_limit
                      let width_limit = page_limit
                    end))

open P

let rec quadratic (n : int): doc =
  if n = 0 then text "line"
  else group (quadratic (n - 1)) <> nl <> text "line"

let () = measure_time (fun size -> render (quadratic size))
