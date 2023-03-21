/-
Tactics for the project
-/

import Init.Tactics
import Mathlib.Tactic.Linarith.Frontend
import Std.Tactic.RCases

open Lean Elab Parser Term Meta Macro Std.Tactic.RCases

/--
`dwi t` (deal with it) is a tactic that runs `t` and then tries to 
solve the goal using `contradiction`, `assumption`, `simp`, and `simpa`.
-/
syntax "dwi " "{" tactic "}" : tactic

macro_rules
  | `(tactic| dwi { $t }) => 
    `(tactic| $t <;> try { first | contradiction | assumption | simp | simpa })