open Printer
open Benchtool

let {page_width; computation_width; _} = setup ~size:20000 "fill-sep"

module P = Printer (DefaultCost (struct
                      let page_width = page_width
                      let computation_width = computation_width
                    end))

open P

let fill_sep xs =
  match xs with
  | [] -> empty
  | x :: xs ->
    let rec loop xs acc =
      match xs with
      | [] -> acc
      | x :: xs -> loop xs ((acc <+> text " " <+> text x) <|> (acc <$> text x))
    in
    loop xs (text x)

let () =
  let lines = Stdio.In_channel.read_lines "/usr/share/dict/words" in
  do_bench (fun size -> print (fill_sep (Core.List.take lines size)))
