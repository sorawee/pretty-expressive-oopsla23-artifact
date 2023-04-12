let param_memo_limit = ref 6
let param_view_cost = ref false
let param_view_memo = ref false

type 's treeof =
  | One of 's
  | Cons of ('s treeof) * ('s treeof)

let tree_flatten (t: 's treeof): 's list =
  let rec loop (t: 's treeof) (acc: 's list) =
    match t with
    | One v -> v :: acc
    | Cons (x, y) -> loop x (loop y acc)
  in loop t []

module type CostFactory =
sig
  type t
  val place : int -> int -> t
  val newline : t
  val combine : t -> t -> t
  val le : t -> t -> bool
  val limit: int
  val debug : t -> string
end

module CorePrinter (C : CostFactory) = struct
  let global_id = ref 0
  let next_id () =
    let id = !global_id in
    global_id := id + 1;
    id

  type measure = { last: int; cost: C.t; layout: string list -> string list }

  let (<==) (m1 : measure) (m2 : measure): bool =
    m1.last <= m2.last && C.le m1.cost m2.cost

  type measure_set =
    | MeasureSet of measure list (* sorted by last in the decreasing order *)
    | Tainted of (unit -> measure)

  type doc =
    { dc: doc_case;
      id: int;
      memo_w: int;
      nl_cnt: int;
      mutable table: ((int, measure_set) Hashtbl.t) option }
  and doc_case =
    | Fail
    | Text of (string treeof) * int
    | Newline
    | Concat of doc * doc
    | Nest of int * doc
    | Align of doc
    | Choice of doc * doc

  let calc1 d = if d.memo_w >= !param_memo_limit then 0 else d.memo_w + 1

  let calc2 d1 d2 =
    let max_weight = max d1.memo_w d2.memo_w in
    if max_weight >= !param_memo_limit then 0 else max_weight + 1

  let fail = { dc = Fail;
               id = next_id ();
               memo_w = 1;
               nl_cnt = 0;
               table = None }
  let nl = { dc = Newline;
             id = next_id ();
             memo_w = 1;
             nl_cnt = 1;
             table = None }

  let make_text s l = { dc = Text (s, l);
                      id = next_id ();
                      memo_w = 1;
                      nl_cnt = 0;
                      table = None }

  let text s = make_text (One s) (String.length s)

  let (<>) (d1 : doc) (d2 : doc) =
    match (d1.dc, d2.dc) with
    | (Fail, _) | (_, Fail) -> fail
    | (Text (_, 0), _) -> d2
    | (_, Text (_, 0)) -> d1
    | (Text (s1, l1), Text (s2, l2)) -> make_text (Cons (s1, s2)) (l1 + l2)
    | _ -> { dc = Concat (d1, d2);
             id = next_id ();
             memo_w = calc2 d1 d2;
             nl_cnt = d1.nl_cnt + d2.nl_cnt;
             table = None }

  let nest (n : int) (d : doc) =
    match d.dc with
    | Fail | Align _ | Text _ -> d
    | _ -> { dc = Nest (n, d);
             id = next_id ();
             memo_w = calc1 d;
             nl_cnt = d.nl_cnt;
             table = None }

  let align d =
    match d.dc with
    | Fail | Align _ | Text _ -> d
    | _ -> { dc = Align d;
             id = next_id ();
             memo_w = calc1 d;
             nl_cnt = d.nl_cnt;
             table = None }

  let (<|>) d1 d2 =
    if d1 == fail then d2
    else if d2 == fail then d1
    else { dc = Choice (d1, d2);
           id = next_id ();
           memo_w = calc2 d1 d2;
           nl_cnt = max d1.nl_cnt d2.nl_cnt;
           table = None }

  let merge (ml1 : measure_set) (ml2 : measure_set): measure_set =
    match (ml1, ml2) with
    | (_, Tainted _) -> ml1
    | (Tainted _, _) -> ml2
    | (MeasureSet ms1, MeasureSet ms2) ->
      let rec loop ms1 ms2 = match (ms1, ms2) with
        | ([], _) -> ms2
        | (_, []) -> ms1
        | (m1 :: ms1p, m2 :: ms2p) ->
          if m1 <== m2 then loop ms1 ms2p
          else if m2 <== m1 then loop ms1p ms2
          else if m1.last > m2.last then m1 :: loop ms1p ms2
          else (* m2.last < m1.last *) m2 :: loop ms1 ms2p
      in MeasureSet (loop ms1 ms2)

  let (++) (m1 : measure) (m2 : measure): measure =
    { last = m2.last;
      cost = C.combine m1.cost m2.cost;
      layout = fun ss -> m1.layout (m2.layout ss) }

  let process_concat
      (process_left : measure -> measure_set)
      (ml1 : measure_set) =
    match ml1 with
    | Tainted mt1 ->
      Tainted (fun () ->
          let m1 = mt1 () in
          match process_left m1 with
          | Tainted mt2 -> m1 ++ mt2 ()
          | MeasureSet (m2 :: _) -> m1 ++ m2
          | _ -> failwith "impossible")
    | MeasureSet ms1 ->
      let do_one (m1 : measure): measure_set =
        let rec loop ms2 result current_best =
          match ms2 with
          | [] -> List.rev (current_best :: result)
          | m2 :: ms2 ->
            let current = m1 ++ m2 in
            if C.le current.cost current_best.cost then loop ms2 result current
            else loop ms2 (current_best :: result) current
        in match process_left m1 with
        | Tainted m2 -> Tainted (fun () -> m1 ++ m2 ())
        | MeasureSet (m2 :: ms2) -> MeasureSet (loop ms2 [] (m1 ++ m2))
        | _ -> failwith "unreachable" in
      let rec fold_right (ms: measure list): measure_set =
        match ms with
        | [] -> failwith "unreachable"
        | [m] -> do_one m
        | m :: ms -> merge (do_one m) (fold_right ms)
      in fold_right ms1

  let memoize f: doc -> int -> int -> measure_set =
    let all_slots = C.limit + 1 in
    let rec g ({ memo_w; table; _ } as d) (c : int) (i : int) =
      if c <= C.limit && i <= C.limit && memo_w = 0 then
        let key = i * all_slots + c in
        match table with
        | None ->
          let tbl = Hashtbl.create 5 in
          d.table <- Some tbl;
          let ml = f g d c i in
          Hashtbl.add tbl key ml;
          ml
        | Some tbl ->
          if Hashtbl.mem tbl key then Hashtbl.find tbl key
          else
            let ml = f g d c i in
            Hashtbl.add tbl key ml;
            ml
      else f g d c i
    in g

  let render (d : doc): string =
    let render self { dc; _ } (c : int) (i : int) : measure_set =
      let core () =
        match dc with
        | Fail -> failwith "fails to render"
        | Text (s, len_s) ->
          MeasureSet [{ last = c + len_s;
                        cost = C.place c len_s;
                        layout = fun ss -> (tree_flatten s) @ ss }]
        | Newline ->
          MeasureSet [{ last = i;
                        cost = (C.combine C.newline (C.place 0 i));
                        layout = fun ss -> "\n" :: String.make i ' ' :: ss }]
        | Concat (d1, d2) ->
          process_concat (fun (m1 : measure) -> self d2 m1.last i) (self d1 c i)
        | Nest (n, d) -> self d c (i + n)
        | Align d -> self d c c
        | Choice (d1, d2) ->
          if d1.nl_cnt < d2.nl_cnt then merge (self d2 c i) (self d1 c i)
          else merge (self d1 c i) (self d2 c i) in
      let exceeds = match dc with
        | Text (_, len) -> (c + len > C.limit) || (i > C.limit)
        | _ -> (c > C.limit) || (i > C.limit) in
      if exceeds then
        Tainted (fun () ->
            match core () with
            | Tainted mt -> mt ()
            | MeasureSet (m :: _) -> m
            | _ -> failwith "impossible")
      else core () in
    let m = match memoize render d 0 0 with
      | MeasureSet (m :: ms) -> m
      | Tainted m ->
        if !param_view_cost then Printf.printf "tainted\n";
        m ()
      | _ -> failwith "impossible" in
    let s = String.concat "" (m.layout []) in

    (* For debugging *)
    if !param_view_cost then
      Printf.printf "last: %d, cost: %s\n" m.last (C.debug m.cost);
    if !param_view_memo then begin
      let (+++) (a, b, c) (d, e, f) = (a + d, b + e, c + f) in
      let visited = Hashtbl.create 1000 in
      let rec count ({ id; table; dc; _ }) =
        if Hashtbl.mem visited id then (0, 0, 0)
        else begin
          Hashtbl.add visited id true;
          let current = match table with
            | None -> (0, 0, 1)
            | Some tbl -> (Hashtbl.length tbl, 1, 1)
          in match dc with
          | Fail | Text _ | Newline -> current
          | Choice (d1, d2) | Concat (d1, d2) ->
            current +++ count d1 +++ count d2
          | Nest (_, d) | Align d -> current +++ count d
        end in
      let (num_entries, num_memo, num_all) = count d in
      Printf.printf "\nall entries: %d\n" num_entries;
      Printf.printf "average entries per node: %f\n"
        ((Float.of_int num_entries) /. (Float.of_int num_memo));
      Printf.printf "nodes with memoization = %d\n" num_memo;
      Printf.printf "all nodes = %d\n" num_all
    end;
    s
end

(* ----------------------------------------------------------------------0---- *)

module type PrinterT =
sig
  type doc

  val fail : doc
  val text : string -> doc
  val (<>) : doc -> doc -> doc
  val (<|>) : doc -> doc -> doc
  val nl : doc
  val align : doc -> doc
  val nest : int -> doc -> doc
  val render : doc -> string

  val group : doc -> doc
  val flatten : doc -> doc
  val flat : doc -> doc
  val (<+>) : doc -> doc -> doc
  val (<$>) : doc -> doc -> doc

  val enclose_sep : doc -> doc -> doc -> doc list -> doc
  val fold_doc : (doc -> doc -> doc) -> doc list -> doc
  val vcat : doc list -> doc
  val hcat : doc list -> doc

  val space : doc
  val comma : doc
  val lbrack : doc
  val rbrack: doc
  val lbrace : doc
  val rbrace : doc
  val lparen : doc
  val rparen : doc
  val dquote : doc
end

module Printer (C : CostFactory): PrinterT = struct
  include CorePrinter (C)

  let space = text " "

  let flatten : doc -> doc =
    let cache = Hashtbl.create 1000 in
    let rec flatten ({ dc = dc; id = id; _ } as d) =
      if Hashtbl.mem cache id then
        Hashtbl.find cache id
      else
        let out = match dc with
          | Fail | Text _ -> d
          | Newline -> space
          | Concat (({ id = a_id; _ } as a), ({ id = b_id; _ } as b)) ->
            let { id = a_idp; _ } as ap = flatten a in
            let { id = b_idp; _ } as bp = flatten b in
            if a_idp = a_id && b_idp = b_id then d else ap <> bp
          | Choice (({ id = a_id; _ } as a), ({ id = b_id; _ } as b)) ->
            let { id = a_idp; _ } as ap = flatten a in
            let { id = b_idp; _ } as bp = flatten b in
            if a_idp = a_id && b_idp = b_id then d else ap <|> bp
          | Nest (_, d) | Align d -> flatten d
        in
        Hashtbl.add cache id out;
        out
    in flatten

  let flat : doc -> doc =
    let cache = Hashtbl.create 1000 in
    let rec flat ({ dc; id; _ } as d) =
      if Hashtbl.mem cache id then
        Hashtbl.find cache id
      else
        let out = match dc with
          | Fail | Text _ -> d
          | Newline -> fail
          | Concat (({ id = a_id; _ } as a), ({ id = b_id; _ } as b)) ->
            let { id = a_idp; _ } as ap = flat a in
            let { id = b_idp; _ } as bp = flat b in
            if a_idp = a_id && b_idp = b_id then d else ap <> bp
          | Choice (({ id = a_id; _ } as a), ({ id = b_id; _ } as b)) ->
            let { id = a_idp; _ } as ap = flat a in
            let { id = b_idp; _ } as bp = flat b in
            if a_idp = a_id && b_idp = b_id then d else ap <|> bp
          | Nest (_, d) | Align d -> flat d
        in
        Hashtbl.add cache id out;
        out
    in flat

  let (<+>) d1 d2 = d1 <> align d2
  let (<$>) d1 d2 = d1 <> nl <> d2
  let group d = d <|> (flatten d)

  (* Arbitrary-choice extensions *)

  let empty = text ""

  let (<->) x y = (flat x) <+> y

  let fold_doc f ds =
    match ds with
    | [] -> empty
    | x :: xs -> List.fold_left f x xs

  let hcat = fold_doc (<->)
  let vcat = fold_doc (<$>)

  let enclose_sep left right sep ds =
    match ds with
    | [] -> left <+> right
    | [d] -> left <+> d <+> right
    | d :: ds ->
      ((hcat (left :: Core.List.intersperse ~sep: sep (d :: ds)))
       <|> (vcat ((left <+> d) :: List.map ((<+>) sep) ds)))
      <+> right

  let comma = text ","
  let lbrack = text "["
  let rbrack = text "]"
  let lbrace = text "{"
  let rbrace = text "}"
  let lparen = text "("
  let rparen = text ")"
  let dquote = text "\""
end

module type Config =
sig
  val width_limit : int
  val limit: int
end

module Cost (C: Config): CostFactory = struct
  type t = int * int
  let limit = C.limit

  let place pos len =
    let stop = pos + len in
    if stop > C.width_limit then
      let start = max C.width_limit pos in
      let a = start - C.width_limit in
      let b = stop - C.width_limit in
      (b * (2*a + b), 0)
    else
      (0, 0)

  let newline = (0, 1)

  let combine (o1, h1) (o2, h2) =
    (o1 + o2, h1 + h2)

  let le (o1, h1) (o2, h2) =
    if o1 = o2 then h1 <= h2 else o1 < o2

  let debug (o, h) = Printf.sprintf "{o: %d, h: %d}" o h
end
