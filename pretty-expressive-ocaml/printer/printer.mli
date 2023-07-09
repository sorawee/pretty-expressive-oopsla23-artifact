val param_memo_limit: int ref
(** A parameter to set memoization weight; positive integer; default = 7 *)

val param_view_cost: bool ref
(** A parameter whether to print cost for debugging; default = false *)

module DefaultCost :
  functor (S : Signature.Config) -> Signature.CostFactory

module Printer :
  functor (C : Signature.CostFactory) -> Signature.PrinterT
