open Pretty_expressive
open Benchtool

let {page_width; computation_width; size; _} = setup ~size:15 "sexp-full"

let cf = Printer.default_cost_factory
    ~page_width:page_width
    ~computation_width:computation_width ()

module P = Printer.MakeCompat (val cf)
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

let (t, _) = test_expr size 0

let doc = pp t

let () = do_bench (fun () -> print doc)
