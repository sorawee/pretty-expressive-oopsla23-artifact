open Printer


module P = Printer (Cost (struct
                      let limit = 100
                      let width_limit = 10
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

let s = render d

let () =
  Printf.printf "%s\n" s
