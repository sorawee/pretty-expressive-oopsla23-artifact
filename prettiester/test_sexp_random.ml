open Printer
open Test_lib

let {page_limit; com_limit; _} = setup ~size:1 ()

module P = Printer (Cost (struct
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

let rec convert v =
  match v with
  | `String s -> Atom s
  | `List xs -> List (List.map convert xs)
  | _ -> failwith "bad"

let () =
  measure_time (fun size ->
      let json = Yojson.Basic.from_file
          ("../benchdata/random-tree-" ^ (string_of_int size) ^ ".sexp") in
      let t = convert json in
      render (pp t))
