module type CostFactory =
sig
  (** The cost factory interface. An instance of a cost factory should also
      satisfy contracts specified in the paper. *)

  type t
  (** A type for cost *)

  val text : int -> int -> t
  (** [text c i] calculate a cost for a text placement at column position [c]
      and indentation level [i] *)

  val newline : int -> t
  (** [newline i] calculates a cost for a newline and indentation at level [i] *)

  val combine : t -> t -> t
  (** [combine x y] combines the costs [x] and [y] together *)

  val le : t -> t -> bool
  (** [le x y] tests if the cost [x] is less than or equal to the cost [y]. *)

  val limit: int
  (** [limit] is a computation width limit. *)

  val debug : t -> string
  (** [debug c] produces a string representation of a cost [c] *)

end

module type PrinterT =
sig
  (** A pretty expressive printer *)

  type doc
  (** The [doc] type *)

  val text : string -> doc
  (** [text s] is a document for textual content [s];
      [s] must not have a newline. *)

  val (<>) : doc -> doc -> doc
  (** [a <> b] is a document for concatenation of documents [a] and [b]
      without alignment. *)

  val (<|>) : doc -> doc -> doc
  (** [a <|> b] is a document for a choice between document [a] and [b]. *)

  val nl : doc
  (** [nl] is a document for a newline. *)

  val align : doc -> doc
  (** [align d] is a document that aligns [d] at the column position. *)

  val nest : int -> doc -> doc
  (** [nest n d] is a document that increments the indentation level by [n]
      when rendering [d] *)

  val print : doc -> string
  (** [print d] prints the document [d] to a string *)

  val flatten : doc -> doc
  (** [flatten d] is a document that removes newlines and indentation spaces
      when rendering [d] *)

  val flat : doc -> doc
  (** [flat d] is a document that imposes a constraint that [d] must not have
      a newline -- an extension of Pi_e *)

  val fail : doc
  (** A document that always fails -- an extension of Pi_e *)

  val group : doc -> doc
  (** [group d] is a shorthand for [d <|> flatten d] *)

  val (<+>) : doc -> doc -> doc
  (** [a <+> b] is a shorthand for [a <> align b] *)

  val (<$>) : doc -> doc -> doc
  (** [a <$> b] is a shorthand for [a <> nl <> b] *)

  val (<->) : doc -> doc -> doc
  (** [a <-> b] is a shorthand for [flat a <+> b].
      This is especially useful when we want to do horizontal concatenation,
      but don't want the left part to have multiple lines. *)

  val enclose_sep : doc -> doc -> doc -> doc list -> doc
  (** [enclose_sep left right sep ds] is a document for a choice between

      {[left d_1 sep d_2 sep ... sep dn right]}

      and

      {[left d_1
        sep d_2
        sep ...
        sep d_n right]}

      where [d_1 d_2 ... d_n] are drawn from [ds], and
      the first style is constrained to not have any newline *)

  val fold_doc : (doc -> doc -> doc) -> doc list -> doc
  (** [fold_doc (++) ds] is a shorthand for [d_1 ++ d_2 ++ ... ++ d_n]
      where [d_1 d_2 ... d_n] are drawn from [ds]. *)

  val vcat : doc list -> doc
  (** [vcat ds] is a shorthand for [d_1 <$> d_2 <$> ... <$> d_n]
      where [d_1 d_2 ... d_n] are drawn from [ds]. *)

  val hcat : doc list -> doc
  (** [vcat ds] is a shorthand for [d_1 <-> d_2 <-> ... <-> d_n]
      where [d_1 d_2 ... d_n] are drawn from [ds]. *)

  val empty : doc
  (** Equivalent to [text ""] *)

  val space : doc
  (** Equivalent to [text " "] *)

  val comma : doc
  (** Equivalent to [text ","] *)

  val lbrack : doc
  (** Equivalent to [text "\["] *)

  val rbrack: doc
  (** Equivalent to [text "\]"] *)

  val lbrace : doc
  (** Equivalent to [text "{"] *)

  val rbrace : doc
  (** Equivalent to [text "}"] *)

  val lparen : doc
  (** Equivalent to [text "("] *)

  val rparen : doc
  (** Equivalent to [text ")"] *)

  val dquote : doc
  (** Equivalent to [text "\""] *)
end

module type Config =
sig
  (** A configuration for the pre-defined cost factory *)

  val width_limit : int
  (** the page width limit *)

  val limit: int
  (** the computation width limit *)
end
