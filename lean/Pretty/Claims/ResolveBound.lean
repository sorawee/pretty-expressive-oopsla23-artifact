import Pretty.Supports.ResolveLast 
import Pretty.Supports.ResolvePareto

/--
A measure set from resolving will have size 
at most $W_\mathcal{F} + 1$ (Lemma 5.9) 
-/
lemma Resolve_bound
    {h_not_empty : ms ≠ []}
    (h : Resolve F d c i (MeasureSet.set ms h_not_empty)) : 
    ms.length ≤ F.W + 1 := by 
  have h_lw := (Resolve_pareto h).left
  cases ms
  case nil => simp
  case cons hd tl =>
    have h_bound : ((hd :: tl).get ⟨(hd :: tl).length - 1 - ((hd :: tl).length - 1), by simp⟩).lw ≥ (hd :: tl).length - 1 := by {
      dwi { apply lw_decreasing_bound }
    }
    simp at h_bound
    have h_last := @Resolve_last _ _ _ _ _ _ hd (by simp) h (by simp)
    simp_arith 
    dwi { apply le_trans }