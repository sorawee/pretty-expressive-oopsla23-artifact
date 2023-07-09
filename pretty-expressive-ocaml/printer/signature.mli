module type CostFactory =
sig
  type t
  val text : int -> int -> t
  val newline : int -> t
  val combine : t -> t -> t
  val le : t -> t -> bool
  val limit: int
  val debug : t -> string
end

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

  val empty : doc
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

module type Config =
sig
  val width_limit : int
  val limit: int
end
