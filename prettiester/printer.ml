let param_memo_limit = ref 7
let param_view_cost = ref false
let param_view_memo = ref false

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

  type measure = { last_width: int;
                   cost: C.t;
                   layout: string list -> string list }

  let (<==) (m1 : measure) (m2 : measure): bool =
    m1.last_width <= m2.last_width && C.le m1.cost m2.cost

  type measure_set =
    (* the list is sorted by cost in the increasing order *)
    | MeasureSet of measure list
    | Tainted of (unit -> measure)

  type doc =
    { dc: doc_case;
      id: int;
      memo_weight: int;
      nl_cnt: int option;
      mutable table: ((int, measure_set) Hashtbl.t) option }
  and doc_case =
    | Fail
    | Text of string
    | Newline
    | Concat of doc * doc
    | Nest of int * doc
    | Align of doc
    | Choice of doc * doc

  let cnt_memo = ref 0
  let cnt_all = ref 0

  let calc1 d =
    if d.memo_weight >= !param_memo_limit then 0
    else d.memo_weight + 1

  let calc2 d1 d2 =
    let max_weight = max d1.memo_weight d2.memo_weight in
    if max_weight >= !param_memo_limit then 0
    else max_weight + 1

  (* constants (next_id is evaluated only once) *)
  let fail = { dc = Fail;
               id = next_id ();
               memo_weight = 1;
               nl_cnt = None;
               table = None }
  let nl = { dc = Newline;
             id = next_id ();
             memo_weight = 1;
             nl_cnt = Some 1;
             table = None }

  (* functions *)
  let text s = { dc = Text s;
                 id = next_id ();
                 memo_weight = 1;
                 nl_cnt = Some 0;
                 table = None }

  let (<>) (d1 : doc) (d2 : doc) =
    (* We can partially evaluate text concatenation, *)
    (* but this requires a better representation of text *)
    (* to avoid O(n^2) from repeated concatenation *)
    if d1 == fail || d2 == fail then fail
    else { dc = Concat (d1, d2);
           id = next_id ();
           memo_weight = calc2 d1 d2;
           nl_cnt = Option.bind d1.nl_cnt (fun nl1 ->
               Option.bind d2.nl_cnt (fun nl2 ->
                   Some (nl1 + nl2))) ;
           table = None }

  let nest (n : int) (d : doc) =
    if d == fail then fail
    else { dc = Nest (n, d);
           id = next_id ();
           memo_weight = calc1 d;
           nl_cnt = d.nl_cnt;
           table = None }

  let align d =
    if d == fail then fail
    else { dc = Align(d);
           id = next_id ();
           memo_weight = calc1 d;
           nl_cnt = d.nl_cnt;
           table = None }

  let (<|>) d1 d2 =
    if d1 == fail then d2
    else if d2 == fail then d1
    else { dc = Choice (d1, d2);
           id = next_id ();
           memo_weight = calc2 d1 d2;
           nl_cnt = Option.bind d1.nl_cnt (fun nl1 ->
               Option.bind d2.nl_cnt (fun nl2 ->
                   Some (max nl1 nl2)));
           table = None }

  let (|||) (ml1 : measure_set) (ml2 : measure_set): measure_set =
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
          else if m1.last_width > m2.last_width then m1 :: loop ms1p ms2
          else (* m2.last_width < m1.last_width *) m2 :: loop ms1 ms2p
      in
      MeasureSet (loop ms1 ms2)

  let (++) (m1 : measure) (m2 : measure): measure =
    { last_width = m2.last_width;
      cost = C.combine m1.cost m2.cost;
      layout = fun ss -> m1.layout (m2.layout ss) }

  let process_concat
      (process_left : measure -> measure_set)
      (ml1 : measure_set) =
    match ml1 with
    | Tainted mt1 ->
      Tainted
        (fun () ->
           let m1 = mt1 () in
           match process_left m1 with
           | Tainted mt2 -> m1 ++ mt2 ()
           | MeasureSet (m2 :: _) -> m1 ++ m2
           | _ -> failwith "impossible")

    | MeasureSet ms1 ->
      let process_one (m1 : measure): measure_set =
        match process_left m1 with
        | Tainted m2 -> Tainted (fun () -> m1 ++ m2 ())
        | MeasureSet ms2 -> MeasureSet (List.map ((++) m1) ms2)
      in match ms1 with
      | [] -> failwith "unreachable"
      | m1 :: tl ->
        List.fold_left (|||) (process_one m1) (List.map process_one tl)


  let memoize f: doc -> int -> int -> measure_set =
    let all_slots = C.limit + 1 in
    let rec g
        ({ memo_weight = memo_weight; table = table; _ } as d)
        (c : int)
        (i : int) =
      if c <= C.limit && i <= C.limit && memo_weight = 0 then
        let key = i * all_slots + c in
        match table with
        | None ->
          let tbl = Hashtbl.create 5 in
          d.table <- Some tbl;
          let ml = f g d c i in
          Hashtbl.add tbl key ml;
          ml
        | Some tbl ->
          if Hashtbl.mem tbl key then
            Hashtbl.find tbl key
          else
            let ml = f g d c i in
            Hashtbl.add tbl key ml;
            ml
      else f g d c i
    in g

  let render (d : doc): string =
    let render self { dc = dc; _ } (c : int) (i : int) : measure_set =
      let core () =
        match dc with
        | Fail -> failwith "fails to render"
        | Text s ->
          let len_s = String.length s in
          MeasureSet [{ last_width = c + len_s;
                        cost = C.place c len_s;
                        layout = fun ss -> s :: ss }]
        | Newline ->
          MeasureSet [{ last_width = i;
                        cost = (C.combine C.newline (C.place 0 i));
                        layout = fun ss -> "\n" :: String.make i ' ' :: ss }]
        | Concat (d1, d2) ->
          process_concat
            (fun (m1 : measure) -> self d2 m1.last_width i)
            (self d1 c i)
        | Nest (n, d) -> self d c (i + n)
        | Align d -> self d c c
        | Choice (d1, d2) ->
          if d1.nl_cnt < d2.nl_cnt then
            (self d2 c i) ||| (self d1 c i)
          else
            (self d1 c i) ||| (self d2 c i) in
      let exceeds = match dc with
        | Text s -> (c + String.length s > C.limit) || (i > C.limit)
        | _ -> (c > C.limit) || (i > C.limit) in
      if exceeds then
        Tainted
          (fun () ->
             match core () with
             | Tainted mt -> mt ()
             | MeasureSet (m :: _) -> m
             | _ -> failwith "impossible")
      else core () in
    let m = match memoize render d 0 0 with
      | MeasureSet (m :: _) -> m
      | Tainted m -> m ()
      | _ -> failwith "impossible" in
    if !param_view_cost then begin
      Printf.printf "last: %d, cost: %s\n" m.last_width (C.debug m.cost);
    end;
    if !param_view_memo then begin
      let (+++) (a, b, c) (d, e, f) = (a + d, b + e, c + f) in
      let visited = Hashtbl.create 1000 in
      let rec count ({ id = id; table = table; dc = dc; _ }) =
        if Hashtbl.mem visited id then
          (0, 0, 0)
        else begin
          Hashtbl.add visited id true;
          let current = match table with
            | None -> (0, 0, 1)
            | Some tbl -> (Hashtbl.length tbl, 1, 1)
          in match dc with
          | Fail | Text _ | Newline -> current
          | Choice (d1, d2) | Concat (d1, d2) -> current +++ count d1 +++ count d2
          | Nest (_, d) | Align d -> current +++ count d
        end in
      let (num_entries, num_memo, num_all) = count d in
      print_newline ();
      Printf.printf "all entries: %d\n" num_entries;
      Printf.printf "average entries per node: %f\n"
        ((Float.of_int num_entries) /. (Float.of_int num_memo));
      Printf.printf "nodes with memoization = %d\n" num_memo;
      Printf.printf "all nodes = %d\n" num_all
    end;

    String.concat "" (m.layout [])
end

(* ----------------------------------------------------------------------0---- *)

module Printer (C : CostFactory) = struct
  include CorePrinter(C)

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
            if a_idp = a_id && b_idp = b_id then d
            else ap <> bp
          | Choice (({ id = a_id; _ } as a), ({ id = b_id; _ } as b)) ->
            let { id = a_idp; _ } as ap = flatten a in
            let { id = b_idp; _ } as bp = flatten b in
            if a_idp = a_id && b_idp = b_id then d
            else ap <|> bp
          | Nest (n, ({ id = id; _ } as a)) ->
            let { id = idp; _ } as ap = flatten a in
            if idp = id then d
            else nest n ap
          | Align ({ id = id; _ } as a) ->
            let { id = idp; _ } as ap = flatten a in
            if idp = id then d
            else align ap in
        Hashtbl.add cache id out;
        out
    in flatten

  let flat : doc -> doc =
    let cache = Hashtbl.create 1000 in
    let rec flat ({ dc = dc; id = id; _ } as d) =
      if Hashtbl.mem cache id then
        Hashtbl.find cache id
      else
        let out = match dc with
          | Fail | Text _ -> d
          | Newline -> fail
          | Concat (({ id = a_id; _ } as a), ({ id = b_id; _ } as b)) ->
            let { id = a_idp; _ } as ap = flat a in
            let { id = b_idp; _ } as bp = flat b in
            if a_idp = a_id && b_idp = b_id then d
            else ap <> bp
          | Choice (({ id = a_id; _ } as a), ({ id = b_id; _ } as b)) ->
            let { id = a_idp; _ } as ap = flat a in
            let { id = b_idp; _ } as bp = flat b in
            if a_idp = a_id && b_idp = b_id then d
            else ap <|> bp
          | Nest (n, ({ id = id; _ } as a)) ->
            let { id = idp; _ } as ap = flat a in
            if idp = id then d
            else nest n ap
          | Align ({ id = id; _ } as a) ->
            let { id = idp; _ } as ap = flat a in
            if idp = id then d
            else align ap in
        Hashtbl.add cache id out;
        out
    in flat

  let (<+>) d1 d2 = d1 <> align d2
  let (<$>) d1 d2 = d1 <> nl <> d2
  let group d = d <|> (flatten d)

  (* Arbitrary-choice extensions *)

  let mt = text ""

  let (<->) x y = (flat x) <+> y

  let fold_doc f ds =
    match ds with
    | [] -> mt
    | x :: xs -> List.fold_left f x xs

  let hcat = fold_doc (<->)
  let vcat = fold_doc (<$>)

  let enclose_sep left right sep ds =
    match ds with
    | [] -> left <+> right
    | [d] -> left <+> d <+> right
    | d :: ds ->
      ((hcat (left :: Core.List.intersperse ~sep: (sep <+> space) (d :: ds)))
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
    if pos + len > C.width_limit then
      (pos + len - max C.width_limit pos, 0)
    else
      (0, 0)

  let newline = (0, 1)

  let combine (a, b) (c, d) =
    (a + c, b + d)

  let le (a, b) (c, d) =
    if a = c then
      b <= d
    else
      a < c

  let debug (o, h) =
    Printf.sprintf "{overflow: %d, height: %d}" o h
end
