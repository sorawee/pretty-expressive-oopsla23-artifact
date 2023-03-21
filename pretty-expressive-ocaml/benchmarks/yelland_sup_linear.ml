open Pretty.Printer
open Benchtool

(* NOTE: May require `ulimit -s <larger-limit>` *)
(*       when the size is large. *)
(*       E.g., the size could be as large as `500` with *)
(*       `ulimit -s 65520` *)
let {page_width; computation_width; size; _} = setup ~size:100 ~page_width:0 "yelland-sup-linear"

let () =
  if not (size > 500) then
    raise (Arg.Bad "bad size")

module P = Printer (DefaultCost (struct
                      let page_width = page_width
                      let computation_width = computation_width
                    end))

open P

(* Begin body *)

(* make an empty document of size n; n >= 1 *)
let rec make_dummy (n : int): doc =
  if n = 1 then text ""
  else text "" <+> make_dummy (n - 1)

(* make n lines; n >= 1 *)
let rec make_lines (n : int): doc =
  if n = 1 then text ""
  else text "" <$> make_lines (n - 1)

(* nth triangle number *)
let tri (n : int): int = n * (n + 1) / 2

let make_choices (k : int): doc =
  let rec loop (i : int): doc =
    let doc =
      (make_lines i) <+>
      text (String.make (tri (k - i + 1)) 'a')
    in if i = 1 then doc else doc <|> loop (i - 1)
  in loop k

let example (k : int): doc =
  let dummy = make_dummy (k * k) in
  let giant = make_choices k in
  dummy <+> giant

let doc = example size

let () = do_bench (fun () -> print doc)
