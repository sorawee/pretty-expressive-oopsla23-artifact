open Printer
open Test_lib

let (page_limit, com_limit) = setup ~size:2 ()

module P = Printer (Cost (struct
                      let limit = com_limit
                      let width_limit = page_limit
                    end))

open P

(* NOTE: Bernardy formats JSON in the Haskell style, which is unconventional *)
(* We follow the style, however, to obtain comparable data points. *)

let rec pp v =
  match v with
  | `Bool b -> if b then text "true" else text "false"
  | `Float f -> text (string_of_float f)
  | `Int n -> text (string_of_int n)
  | `Null -> text "null"
  | `String s ->
    (* We are being very crude here and don't care about escaping *)
    dquote <+> text s <+> dquote
  | `List xs ->
    let xs = List.map pp xs in enclose_sep lbrack rbrack comma xs
  | `Assoc obj ->
    let obj = List.sort (fun (k1, _) (k2, _) -> String.compare k1 k2) obj in
    let xs = List.map (fun (k, v) -> text ("\"" ^ k ^ "\": ") <+> pp v) obj in
    enclose_sep lbrace rbrace comma xs
  | _ -> failwith "bad"

let () =
  let json_big = Yojson.Basic.from_file "../artifacts/benchdata/10k.json" in
  let json_small = Yojson.Basic.from_file "../artifacts/benchdata/1k.json" in
  measure_time (fun size ->
      if size = 1 || size = 2 then
        render (pp (if size = 1 then json_small else json_big))
      else
        raise (Arg.Bad "bad size"))
