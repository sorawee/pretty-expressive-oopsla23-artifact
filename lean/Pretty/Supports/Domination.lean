import Pretty.Defs.Basic
import Pretty.Supports.FactoryMath

/-! 
## Various lemmas about domination
-/

lemma dominates_refl (F : Factory α) : dominates F m m := by {
  simp [dominates, Factory.le_refl]
}

lemma dominates_trans {F : Factory α} (h : dominates F m₁ m₂) (h' : dominates F m₂ m₃) : dominates F m₁ m₃ := by {
  simp [dominates] at * 
  constructor 
  case left => 
    apply le_trans 
    . apply h.left 
    . apply h'.left
  case right => 
    apply F.le_trans 
    . apply h.right
    . apply h'.right
}

inductive FourCases (F : Factory α) (m₁ m₂ : Meas) : Prop where 
  | first_dom  (h_dom : dominates F m₁ m₂)
  | second_dom (h_non_dom : ¬ (dominates F m₁ m₂)) 
               (h_dom : dominates F m₂ m₁) 
  | first_last (h_non_dom₁ : ¬ (dominates F m₁ m₂)) 
             (h_non_dom₂ : ¬ (dominates F m₂ m₁))
             (h : m₁.last > m₂.last) 
  | second_last (h_non_dom₁ : ¬ (dominates F m₁ m₂)) 
              (h_non_dom₂ : ¬ (dominates F m₂ m₁))
              (h : m₂.last > m₁.last) 

/--
In the `merge` operation, there are four possible cases
based on domination of two measures. 
This lemma creates an exhaustive case analysis for these four cases.
-/
lemma four_cases (F : Factory α) (m₁ m₂ : Meas) : FourCases F m₁ m₂ := by {
  cases lt_trichotomy m₁.last m₂.last
  case inl h => 
    simp [h, le_of_lt h]
    by_cases F.le m₁.cost m₂.cost = true
    case pos h' => 
      apply FourCases.first_dom
      case h_dom => 
        simp only [
          dominates, Bool.decide_and, Bool.decide_coe, 
          Bool.and_eq_true, decide_eq_true_eq
        ]
        dwi { constructor }
        case left => 
          apply le_of_lt
          assumption
    case neg h' => 
      dwi { apply FourCases.second_last } 
      case h_non_dom₁ => 
        simp only [
          dominates, Bool.decide_and, Bool.decide_coe, 
          Bool.and_eq_true, decide_eq_true_eq, not_and, Bool.not_eq_true
        ]
        intro
        simp at h
        assumption
      case h_non_dom₂ => 
        simp only [
          dominates, Bool.decide_and, Bool.decide_coe,
          Bool.and_eq_true, decide_eq_true_eq, not_and, Bool.not_eq_true
        ]
        intro
        replace h' := not_le_of_lt h' 
        contradiction
  case inr h =>
    cases h 
    case inl h' => 
      simp [h']
      by_cases F.le m₁.cost m₂.cost = true
      case pos => 
        apply FourCases.first_dom 
        case h_dom => 
          simp [dominates]
          dwi { constructor } 
          case left => simp [h']
      case neg =>
        apply FourCases.second_dom
        case h_non_dom =>
          simp [dominates]
          intro
          simp at h 
          assumption
        case h_dom => 
          simp [dominates]
          constructor
          case left => 
            apply le_of_eq
            symm
            assumption
          case right => 
            apply Factory.le_of_lt
            case h₁ => simp [← Factory.not_le_iff_lt, h]
    case inr h' => 
      by_cases Factory.le F m₂.cost m₁.cost = true
      case pos => 
        apply FourCases.second_dom 
        case h_non_dom => 
          simp [dominates]
          intro
          replace h' := not_le_of_lt h' 
          contradiction
        case h_dom => 
          simp [dominates]
          dwi { constructor }
          case left => 
            apply le_of_lt 
            assumption
      case neg => 
        dwi { apply FourCases.first_last } 
        case h_non_dom₁ => 
          simp [dominates]
          intro
          replace h' := not_le_of_lt h' 
          contradiction
        case h_non_dom₂ => 
          simp [dominates]
          intro 
          simp at h
          assumption
}