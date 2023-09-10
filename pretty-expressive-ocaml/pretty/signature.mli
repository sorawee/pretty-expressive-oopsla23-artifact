(** This entire module defines types for the pretty printer. *)

module type CostFactory =
sig
  (** The cost factory interface. An instance of a cost factory should also
      satisfy contracts specified in the paper. *)

  type t
  (** A type for cost *)

  val text : int -> int -> t
  (** [text c i] calculates a cost for a text placement at column position [c]
      and indentation level [i] *)

  val newline : int -> t
  (** [newline i] calculates a cost for a newline and indentation at level [i] *)

  val combine : t -> t -> t
  (** [combine x y] combines the costs [x] and [y] together *)

  val le : t -> t -> bool
  (** [le x y] tests if the cost [x] is less than or equal to the cost [y]. *)

  val limit: int
  (** [limit] is the computation width limit. *)

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
      [s] must not contain a newline. *)

  val (<>) : doc -> doc -> doc
  (** [a <> b] is a document for concatenation of documents [a] and [b]
      without alignment. *)

  val (<|>) : doc -> doc -> doc
  (** [a <|> b] is a document for a choice between document [a] and [b]. *)

  val nl : doc
  (** [nl] is a document for a newline that [flatten]s to a single space. *)

  val break : doc
  (** [break] is a document for a newline that [flatten]s to an empty string. *)

  val hard_nl : doc
  (** [hard_nl] is a document for a newline that [fail]s to [flatten]. *)

  val newline : (string option) -> doc
  (** [newline s] is a document for a newline.
      When [s] is [None], it [flatten]s to [fail].
      When [s] is not [None], it [flatten]s to the specified [text]. *)

  val align : doc -> doc
  (** [align d] is a document that aligns [d] at the column position. *)

  val nest : int -> doc -> doc
  (** [nest n d] is a document that increments the indentation level by [n]
      when rendering [d] *)

  val reset : doc -> doc
  (** [reset d] is a document that resets indentation level to 0 in [d] *)

  val print : doc -> Info.info
  (** [print d] prints the document [d] to an [info] record. *)

  val pretty_print : doc -> string
  (** [pretty_print d] prints the document [d] to a string. *)

  val flatten : doc -> doc
  (** [flatten d] is a document that replaces newlines and indentation spaces
      with what's specified in [newline] when rendering [d] *)

  val fail : doc
  (** A document that always fails -- an extension of Pi_e *)

  val group : doc -> doc
  (** [group d] is a shorthand for [d <|> flatten d] *)

  val (<+>) : doc -> doc -> doc
  (** [a <+> b] is a shorthand for [a <> align b] *)

  val (<$>) : doc -> doc -> doc
  (** [a <$> b] is a shorthand for [a <> hard_nl <> b] *)

  val (<->) : doc -> doc -> doc
  (** [a <-> b] is a shorthand for [flatten a <+> b].
      This is especially useful when combined with [hard_nl].
      It is used when we want to do horizontal concatenation,
      but don't want the left part to have multiple lines. *)

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

  val page_width : int
  (** the page width limit *)

  val computation_width: int
  (** the computation width limit *)
end
