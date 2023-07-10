open Printer
open Benchtool

(* NOTE: size must be an integer <= 255 *)
let {page_width; computation_width; size; _} = setup ~size:255 ~width:0 "yelland-dag"

let () =
  if not (size > 255) then
    raise (Arg.Bad "bad size")

module P = Printer (DefaultCost (struct
                      let page_width = page_width
                      let computation_width = computation_width
                    end))

open P

let chr (n : int): doc = text (String.make 1 (char_of_int n))

let rec mk (n : int): doc =
  if n = 0 then text "X"
  else let subdoc = mk (n - 1) in (chr n <> subdoc <> chr n) <|> subdoc

let () = do_bench (fun size -> print (mk size))
