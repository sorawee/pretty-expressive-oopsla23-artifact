import Pretty.Defs.Basic
import Pretty.Supports.MergeBasic

/-!
Various measure set operations (Figure 12), which consist of:
-/

/--
- lift;
-/
def MeasureSet.lift (f : @Meas α → @Meas α) : @MeasureSet α → @MeasureSet α
  | MeasureSet.tainted m => MeasureSet.tainted (f m)
  | MeasureSet.set ms h => MeasureSet.set (ms.map f) (by simp [h])

/--
- taint; and
-/
def MeasureSet.taint : @MeasureSet α → @MeasureSet α
  | MeasureSet.tainted m => MeasureSet.tainted m
  | MeasureSet.set ms h => MeasureSet.tainted (ms.head h)

/--
- union (⊎)
-/
def MeasureSet.union (F : Factory α) : @MeasureSet α → @MeasureSet α → @MeasureSet α
  | s, MeasureSet.tainted _ => s
  | MeasureSet.tainted _, MeasureSet.set ms h => MeasureSet.set ms h
  | MeasureSet.set ms₁ h₁, MeasureSet.set ms₂ _ => 
    MeasureSet.set (merge F ⟨ms₁, ms₂⟩) (by {
      apply merge_not_empty 
      simp [h₁]
    })