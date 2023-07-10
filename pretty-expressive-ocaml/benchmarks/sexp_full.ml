open Printer
open Benchtool

let {page_limit; com_limit; _} = setup ~size:15 ()

module P = Printer (DefaultCost (struct
                      let limit = com_limit
                      let width_limit = page_limit
                    end))

open P

let hsep  = fold_doc (fun x y -> x <+> space <+> y)
let sep xs  = hsep xs <|> vcat xs

type sexpr =
  | List of sexpr list
  | Atom of string

let rec pp v =
  match v with
  | List xs -> lparen <+> sep (List.map pp xs) <+> rparen
  | Atom x -> text x

let rec test_expr n c =
  if n = 0 then
    (Atom (string_of_int c), c + 1)
  else
    let (t1 , c1) = test_expr (n - 1) c in
    let (t2 , c2) = test_expr (n - 1) c1 in
    (List [t1; t2], c2)

let () =
  measure_time (fun size ->
      let (t, _) = test_expr size 0 in
      print (pp t))
