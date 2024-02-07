open Pretty_expressive
open Benchtool

(* NOTE: size must be an integer <= 255 *)
let {page_width; computation_width; size; _} = setup ~size:255 ~page_width:0 "yelland-dag"

let () =
  if not (size > 255) then
    raise (Arg.Bad "bad size")

let cf = Printer.default_cost_factory
    ~page_width:page_width
    ~computation_width:computation_width ()

module P = Printer.MakeCompat (val cf)
open P

let chr (n : int): doc = text (String.make 1 (char_of_int n))

let rec mk (n : int): doc =
  if n = 0 then text "X"
  else let subdoc = mk (n - 1) in (chr n <> subdoc <> chr n) <|> subdoc

let doc = mk size

let () = do_bench (fun () -> print doc)
