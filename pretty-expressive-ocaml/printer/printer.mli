(**  This module provides a pretty expressive printer. *)

val param_memo_limit: int ref
(** A parameter to set the memoization weight. It must be positive. Defaults to [7] *)

val param_view_cost: bool ref
(** A parameter saying whether to print the cost, for debugging purposes. Defaults to [false] *)

module DefaultCost :
  functor (Config : Signature.Config) -> Signature.CostFactory
(** A pre-defined cost factory, configurable by the page width limit
    and computation width limit *)

module Printer :
  functor (CostFactory : Signature.CostFactory) -> Signature.PrinterT
(** The pretty printer and doc combinators, parameterized by a cost factory *)
