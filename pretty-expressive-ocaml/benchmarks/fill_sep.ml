open Printer
open Benchtool

let {page_limit; com_limit; _} = setup ~size:20000 ()

module P = Printer (DefaultCost (struct
                      let limit = com_limit
                      let width_limit = page_limit
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
  measure_time (fun size -> render (fill_sep (Core.List.take lines size)))
