open Printer
open Test_lib

(* NOTE: size must be an integer <= 255 *)
let {page_limit; com_limit; size; _} = setup ~size:255 ~width:0 ()

let () =
  if not (size > 255) then
    raise (Arg.Bad "bad size")

module P = Printer (Cost (struct
                      let limit = com_limit
                      let width_limit = page_limit
                    end))

open P

let chr (n : int): doc = text (String.make 1 (char_of_int n))

let rec mk (n : int): doc =
  if n = 0 then text "X"
  else let subdoc = mk (n - 1) in (chr n <> subdoc <> chr n) <|> subdoc

let () = measure_time (fun size -> render (mk size))
