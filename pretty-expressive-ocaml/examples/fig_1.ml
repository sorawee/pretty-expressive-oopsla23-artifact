open Printer

module P = Printer (DefaultCost (struct
                      let limit = 100
                      let width_limit = 80
                    end))

open P

let () =
  param_view_cost := true

let d =
  text "function append(first,second,third){"
  <> nest 4 (
    let f = text "first +" in
    let s = text "second +" in
    let t = text "third" in
    nl <> text "return " <> (
      (text "(" <> (nest 4 (nl <> (f <$> s <$> t))) <$> text ")") <|>
      let sp = text " " in (f <> sp <> s <> sp <> t)
    )
  ) <$> text "}"

let () =
  Printf.printf "%s\n" (print d)
