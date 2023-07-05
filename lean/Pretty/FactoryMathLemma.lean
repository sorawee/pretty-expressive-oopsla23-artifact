import Pretty.FactoryDef
import Pretty.Tactic

/-!
Basic facts about cost factories.
-/

namespace Factory 

def lt (F : Factory α) (c₁ c₂ : α) : Prop :=
  F.le c₁ c₂ ∧ c₁ ≠ c₂

section FactoryImplicit

variable {F : Factory α}

lemma le_refl (c : α) : F.le c c := by 
  dwi { cases F.le_total c c }

lemma not_eq_of_not_le (h : ¬ F.le c₁ c₂) : c₁ ≠ c₂ := by 
  intro h'
  subst h'
  contrapose h 
  simp only [Bool.not_eq_true, Bool.not_eq_false]
  apply le_refl 

lemma not_le_iff_lt : ¬ F.le c₁ c₂ ↔ F.lt c₂ c₁ := by 
  constructor
  case mp => 
    intro h
    simp only [lt, ne_eq]
    dwi { cases F.le_total c₂ c₁ }
    case inl h' => 
      simp only [h', true_and]
      intro h 
      dwi { apply not_eq_of_not_le }
      . symm 
        assumption
  case mpr => 
    intro h 
    simp [lt] at *
    let ⟨h₁, h₂⟩ := h
    contrapose h₂
    simp only [ne_eq, Bool.not_eq_false] at h₂
    have h' := F.le_antisymm h₁ h₂
    simpa

lemma lt_trans (h₁ : F.lt c₁ c₂) (h₂ : F.lt c₂ c₃) : F.lt c₁ c₃ := by
  simp only [lt, ne_eq] at *
  let ⟨h₁, _⟩ := h₁
  let ⟨h₂, _⟩ := h₂
  constructor 
  case left => dwi { apply F.le_trans }
  case right => 
    intro h
    subst h
    dwi { have := F.le_antisymm h₁ h₂}

lemma le_of_lt (h₁ : F.lt c c') : F.le c c' := by
  simp only [lt, ne_eq] at h₁
  simp [h₁]

lemma invalid_inequality (h₁ : F.le c₁ c₂) (h₂ : F.lt c₂ c₃) (h₃ : F.le c₃ c₁) : False := by
  simp [lt] at h₂ 
  have h_trans := F.le_trans h₁ h₂.left 
  have h := F.le_antisymm h_trans h₃ 
  subst h
  have h := F.le_antisymm h₁ h₂.left 
  subst h 
  simp at h₂

end FactoryImplicit

end Factory