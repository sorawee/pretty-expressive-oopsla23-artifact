open Pretty_expressive
open Benchtool

let {page_width; computation_width; size; _} = setup ~size:20000 "fill-sep"

let cf = Printer.default_cost_factory
    ~page_width:page_width
    ~computation_width:computation_width ()

module P = Printer.MakeCompat (val cf)
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

let lines = Stdio.In_channel.read_lines (Sys.getenv "BENCHDATA" ^ "/words")

let doc = fill_sep (Core.List.take lines size)

let () = do_bench (fun () -> print doc)
