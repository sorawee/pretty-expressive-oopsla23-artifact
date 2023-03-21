open Pretty.Printer

let print_three (width: int) =
  let module P = Printer (DefaultCost (struct
                            let computation_width = 100
                            let page_width = width
                          end)) in
  let open P in

  (* Page 2, Figure 1a *)
  let d_traditional =
    text "function append(first,second,third){"
    <> nest 4 (
      let f = text "first +" in
      let s = text "second +" in
      let t = text "third" in
      nl <> text "return " <>
      group (nest 4 (f <> nl <> s <> nl <> t))
    ) <> nl <> text "}" in

  (* Page 2, Figure 1b *)
  let d_arbitrary =
    text "function append(first,second,third){" <$>
    ( let f = text "first +" in
      let s = text "second +" in
      let t = text "third" in
      let sp = text " " in
      let indentation = text "    " in
      let ret = text "return " in
      indentation <+>
      (((ret <+> text "(") <$>
        (indentation <+> (f <$> s <$> t)) <$>
        text ")") <|>
       (ret <+> f <+> sp <+> s <+> sp <+> t)))
    <$> text "}" in

  (* Page 11 *)
  let d_pretty_expressive =
    text "function append(first,second,third){" <> nest 4 (
      let f = text "first +" in let s = text "second +" in let t = text "third" in
      nl <> text "return " <>
      ((text "(" <> (nest 4 (nl <> (f <> nl <> s <> nl <> t))) <> nl <> text ")") <|>
       let sp = text " " in (f <> sp <> s <> sp <> t))
    ) <> nl <> text "}" in

  Printf.printf "%s\n" (pretty_print d_traditional);
  Printf.printf "%s\n" (pretty_print d_arbitrary);
  Printf.printf "%s\n" (pretty_print d_pretty_expressive);
  ()

let () = print_three 22
let () = print_three 36
