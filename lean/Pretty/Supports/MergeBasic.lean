import Pretty.Defs.Basic
import Pretty.Supports.Domination

lemma merge_not_empty (h : ms₁ ≠ [] ∨ ms₂ ≠ []) : 
    @merge _ F ⟨ms₁, ms₂⟩ ≠ [] := by 
  induction ms₁ generalizing ms₂
  case nil => 
    dwi { cases h }
    case inr => simpa [merge]
  case cons m₁ ms₁ ih₁ =>
    induction ms₂
    case nil => dwi { cases h }
    case cons m₂ ms₂ ih₂ =>
      cases four_cases F m₁ m₂
      case first_dom | second_dom => 
        simp [merge, *]
      case first_last => 
        simp [merge, *]
      case second_last =>
        have : ¬ m₁.last > m₂.last := by linarith
        simp [merge, *]