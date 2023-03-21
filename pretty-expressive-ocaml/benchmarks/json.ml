open Pretty.Printer
open Benchtool

let {page_width; computation_width; size; _} = setup ~size:2 "json"

let json_file =
  match size with
  | 1 -> "/1k.json"
  | 2 -> "/10k.json"
  | _ -> raise (Arg.Bad "bad size")

module P = Printer (DefaultCost (struct
                      let page_width = page_width
                      let computation_width = computation_width
                    end))

open P

(* NOTE: Bernardy's paper formats JSON in the Haskell style, *)
(* which is unconventional. We follow the style, however, *)
(* to obtain comparable data points. *)

let enclose_sep left right sep ds =
  match ds with
  | [] -> left <+> right
  | [d] -> left <+> d <+> right
  | d :: ds ->
    ((hcat (left :: Core.List.intersperse ~sep: sep (d :: ds)))
     <|> (vcat ((left <+> d) :: List.map ((<+>) sep) ds)))
    <+> right

let rec pp v =
  match v with
  | `Bool b -> if b then text "true" else text "false"
  | `Float f -> text (string_of_float f)
  | `Int n -> text ((string_of_int n) ^ ".0")
  | `Null -> text "null"
  | `String s -> dquote <+> text s <+> dquote
  | `List xs ->
    let xs = List.map pp xs in enclose_sep lbrack rbrack comma xs
  | `Assoc obj ->
    let obj = List.sort (fun (k1, _) (k2, _) -> String.compare k1 k2) obj in
    let xs = List.map (fun (k, v) -> text ("\"" ^ k ^ "\": ") <+> pp v) obj in
    enclose_sep lbrace rbrace comma xs
  | _ -> failwith "bad"

let json = Yojson.Basic.from_file (Sys.getenv "BENCHDATA" ^ json_file)

let doc = pp json

let () = do_bench (fun () -> print doc)
