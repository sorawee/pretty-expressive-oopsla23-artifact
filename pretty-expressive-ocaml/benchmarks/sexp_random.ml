open Pretty.Printer
open Benchtool

let {page_width; computation_width; size; _} = setup ~size:1 "sexp-random"

module P = Printer (DefaultCost (struct
                      let page_width = page_width
                      let computation_width = computation_width
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

let json = Yojson.Basic.from_file
    (Sys.getenv "BENCHDATA"  ^ "/random-tree-" ^ string_of_int size ^ ".sexp")

let doc = pp (convert json)

let () = do_bench (fun () -> print doc)
