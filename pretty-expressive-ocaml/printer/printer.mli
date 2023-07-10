(**  This module provides a pretty expressive printer. *)

val param_memo_limit: int ref
(** A parameter to set memoization weight; positive integer; default is [7] *)

val param_view_cost: bool ref
(** A parameter whether to print cost for debugging; default is [false] *)

module DefaultCost :
  functor (Config : Signature.Config) -> Signature.CostFactory
(** A pre-defined cost factory, configurable by the page width limit
    and computation width limit *)

module Printer :
  functor (CostFactory : Signature.CostFactory) -> Signature.PrinterT
(** The pretty printer and doc combinators, parameterized by a cost factory *)
