import Pretty.Defs.Basic
import Pretty.Supports.Pareto
import Pretty.Supports.MergeBasic

lemma merge_first_dom (ms₁ : List Meas) 
    (h_pareto₂ : pareto F (m₂ :: ms₂))
    (h_dom : dominates F m₁ m₂) :
    ∃ n, merge F ⟨m₁ :: ms₁, m₂ :: ms₂⟩ = m₁ :: merge F ⟨ms₁, ms₂.drop n⟩ ∧ 
         ∀ (m : Meas), m ∈ ms₂.take n → dominates F m₁ m := by 
  -- Let (x,y) be a measure with lw x and cost y
  -- (5,6) ..... union (6,7) (5,8) ... 
  
  -- Looks like a weird thing to induct on, but it works...
  induction ms₂
  case nil => 
    exists 0
    cases ms₁ <;> simp [merge, h_dom]
  case cons hd tl ih => 
    specialize ih (pareto_rest' h_pareto₂)
    cases four_cases F m₁ hd
    case first_dom h_dom_hd => 
      -- (5,6) ..... union [(6,7) (5,8)] (4,9)
      simp [merge, h_dom, h_dom_hd] at ih ⊢ 
      let ⟨n, ⟨h_left, h_right⟩⟩ := ih
      exists n + 1
      constructor
      case left => simp [h_left]
      case right => 
        intro m h 
        simp at h
        cases h 
        case inl h => subst h; assumption
        case inr h => exact h_right _ h
    case second_dom h_non_dom h_bad => 
      -- (5,6) ..... union (6,7) (4,3) ... impossible
      replace h_pareto₂ := pareto_head h_pareto₂
      simp at h_pareto₂
      simp [dominates] at h_bad h_dom
      cases F.invalid_inequality h_dom.right h_pareto₂.right h_bad.right
    case first_lw h_non_dom₁ h_non_dom₂ h_lw => 
      -- (5,6) ..... union [(10,7)] (1,9) ...
      simp [merge, h_non_dom₁, h_non_dom₂, h_lw, h_dom]
      exists 0
      simp
    case second_lw h_non_dom₁ _ _ => 
      -- (5,6) ..... union [(10,7)] (8,3) ... impossible
      --  m₁                   m₂    hd
      simp [dominates] at h_dom h_non_dom₁ 
      specialize h_non_dom₁ (by {
        apply Nat.le_of_lt 
        assumption
      })
      replace h_pareto₂ := pareto_head h_pareto₂
      have h' := @Factory.not_le_iff_lt _ F
      simp at h' 
      rw [h'] at h_non_dom₁
      have h_trans := F.lt_trans h_pareto₂.right h_non_dom₁
      rw [←Factory.not_le_iff_lt] at h_trans
      replace h_trans := h_trans h_dom.right
      contradiction

lemma merge_second_dom (ms₂ : List Meas) 
    (h_pareto₁ : pareto F (m₁ :: ms₁))
    (h_dom : dominates F m₂ m₁)
    (h_non_dom : ¬ dominates F m₁ m₂) :
    ∃ n, (merge F ⟨m₁ :: ms₁, m₂ :: ms₂⟩) = m₂ :: (merge F ⟨ms₁.drop n, ms₂⟩) ∧
         ∀ (m : Meas), m ∈ ms₁.take n → dominates F m₂ m := by 
  --  (6,7) (5,8) ...  union (5,6) ......
  induction ms₁
  case nil => 
    exists 0
    simp [merge, h_dom]
    intro
    contradiction
  case cons hd tl ih => 
    specialize ih (pareto_rest' h_pareto₁)
    cases four_cases F hd m₂
    case first_dom h_bad => 
      replace h_pareto₁ := pareto_head h_pareto₁
      simp [dominates] at h_bad h_dom
      cases F.invalid_inequality h_dom.right h_pareto₁.right h_bad.right
    case second_dom h_non_dom_hd h_dom_hd => 
      simp [merge, *] at ih ⊢ 
      let ⟨n, ⟨h_left, h_right⟩⟩ := ih
      exists (n + 1)
      constructor 
      case left => simp [h_left]
      case right => 
        simp [h_dom_hd]
        intros m h
        exact h_right _ h
    case first_lw h_non_dom₁ h_non_dom₂ h_lw => 
      --  (10,20) (7,1) ...  union (5,6) ......
      simp [dominates] at h_dom h_non_dom₂
      specialize h_non_dom₂ (by {
        apply Nat.le_of_lt
        simp [h_lw]
      })
      replace h_pareto₁ := pareto_head h_pareto₁
      have h' := @Factory.not_le_iff_lt _ F
      simp at h' 
      rw [h'] at h_non_dom₂
      have h_trans := F.lt_trans h_pareto₁.right h_non_dom₂
      rw [←Factory.not_le_iff_lt] at h_trans
      replace h_trans := h_trans h_dom.right
      contradiction
    case second_lw h_non_dom₁ h_non_dom₂ h_lw => 
      replace h_lw := Nat.not_lt_of_lt h_lw
      simp [merge, *]
      exists 0
      simp

lemma merge_head_either 
    (h_pareto₁ : pareto F (m₁ :: ms₁)) 
    (h_pareto₂ : pareto F (m₂ :: ms₂)) : 
    m₁ = List.head (merge F ⟨m₁ :: ms₁, m₂ :: ms₂⟩) (by { apply merge_not_empty; simp }) ∨ 
    m₂ = List.head (merge F ⟨m₁ :: ms₁, m₂ :: ms₂⟩) (by { apply merge_not_empty; simp }) := by {
  cases four_cases F m₁ m₂
  case first_dom h_dom => 
    left 
    let ⟨_, ⟨_, _⟩⟩ := merge_first_dom ms₁ h_pareto₂ h_dom
    rw [← List.get_zero_eq_head, List.get_of_eq]
    case h.h => assumption
    case h => simp [merge]
  case second_dom h_non_dom h_dom => 
    right
    let ⟨_, ⟨_, _⟩⟩ := merge_second_dom ms₂ h_pareto₁ h_dom h_non_dom
    rw [← List.get_zero_eq_head, List.get_of_eq]
    case h.h => assumption
    case h => simp [merge]
  case first_lw => simp [merge, *]
  case second_lw => 
    have : ¬ (m₁.lw > m₂.lw) := by linarith
    simp [merge, *]
}

lemma merge_preserves_pareto 
    (h_pareto₁ : pareto F ms₁) (h_pareto₂ : pareto F ms₂) : 
    pareto F (merge F ⟨ms₁, ms₂⟩) := by
  induction ms₁ generalizing ms₂
  case nil => simpa [merge]
  case cons m₁ ms₁ ih₁ => 
    induction ms₂
    case nil => 
      simpa [merge]
    case cons m₂ ms₂ ih₂ => 
      simp [merge]
      cases four_cases F m₁ m₂
      case first_dom h_dom => 
        simp [h_dom]
        apply ih₂
        apply pareto_rest 
        assumption
      case second_dom h_non_dom h_dom => 
        simp [h_non_dom, h_dom]
        dwi { apply ih₁ }
        case h_pareto₁ => 
          apply pareto_rest
          assumption
      case first_lw h_non_dom₁ h_non_dom₂ h_lw => 
        simp [h_non_dom₁, h_non_dom₂, h_lw]
        cases ms₁
        case nil => 
          simp [merge]
          dwi { apply pareto_cons } 
          case h_cost => 
            rw [←Factory.not_le_iff_lt]
            simp [dominates] at h_non_dom₂
            simp [h_non_dom₂ (Nat.le_of_lt h_lw)]
        case cons hd tl => 
          cases h_merge : merge F (hd :: tl, m₂ :: ms₂)
          case nil => apply pareto_one 
          case cons => 
            apply pareto_cons 
            case h_lw => 
              have h_pareto₁' := pareto_rest h_pareto₁
              cases merge_head_either h_pareto₁' h_pareto₂
              case inl h => 
                replace h_pareto₁ := pareto_head h_pareto₁
                simp [h_merge] at h
                subst h
                simp [h_pareto₁]
              case inr h => 
                simp [h_merge] at h
                simpa [← h]
            case h_cost => 
              have h_pareto₁' := pareto_rest h_pareto₁
              cases merge_head_either h_pareto₁' h_pareto₂
              case inl h => 
                simp [← h]
                replace h_pareto₁ := pareto_head h_pareto₁
                simp [h_merge] at h
                rw [h] at h_pareto₁
                simp [h_pareto₁]
              case inr h => 
                rw [←Factory.not_le_iff_lt]
                simp [h_merge] at h
                subst h
                simp [dominates] at h_non_dom₂
                simp [h_non_dom₂ (Nat.le_of_lt h_lw)]
            case h => 
              rw [← h_merge] 
              dwi { apply ih₁ }
              case h_pareto₁ => 
                apply pareto_rest
                assumption
      case second_lw h_non_dom₁ h_non_dom₂ h_lw => 
        have : ¬ (m₁.lw > m₂.lw) := by linarith
        simp [h_non_dom₁, h_non_dom₂, this]
        cases ms₂
        case nil => 
          simp [merge]
          dwi { apply pareto_cons } 
          case h_cost => 
            rw [←Factory.not_le_iff_lt]
            simp [dominates] at h_non_dom₁
            simp [h_non_dom₁ (Nat.le_of_lt h_lw)]
        case cons hd tl => 
          cases h_merge : merge F (m₁ :: ms₁, hd :: tl)
          case nil => apply pareto_one
          case cons => 
            apply pareto_cons 
            case h_lw => 
              have h_pareto₂' := pareto_rest h_pareto₂
              cases merge_head_either h_pareto₁ h_pareto₂'
              case inl h => 
                simp [h_merge] at h
                simpa [← h]
              case inr h => 
                simp [h_merge] at h
                subst h
                replace h_pareto₂ := pareto_head h_pareto₂
                simp [h_pareto₂]
            case h_cost => 
              have h_pareto₂' := pareto_rest h_pareto₂
              cases merge_head_either h_pareto₁ h_pareto₂'
              case inl h => 
                rw [←Factory.not_le_iff_lt]
                simp [h_merge] at h
                simp [← h]
                simp [dominates] at h_non_dom₁
                simp [h_non_dom₁ (Nat.le_of_lt h_lw)]
              case inr h => 
                simp [h_merge] at h
                subst h
                replace h_pareto₂ := pareto_head h_pareto₂
                simp [h_pareto₂]
            case h => 
              rw [← h_merge]
              apply ih₂
              apply pareto_rest
              assumption

lemma merge_pareto_subset (h_in : m ∈ merge F ⟨ms₁, ms₂⟩) 
    (h_pareto₁ : pareto F ms₁) (h_pareto₂ : pareto F ms₂) : 
    m ∈ ms₁ ∨ m ∈ ms₂ := by {
  generalize h : merge _ _ = rms at h_in 
  dwi { induction rms generalizing ms₁ ms₂ }
  case cons hd tl ih => 
    cases h_in 
    case head => 
      cases ms₁
      case nil => 
        simp [merge] at h
        subst h 
        simp 
      case cons m₁ ms₁ => 
        cases ms₂
        case nil => 
          simp [merge] at h
          obtain ⟨hl, -⟩ := h 
          subst hl 
          simp 
        case cons m₂ ms₂ => 
          cases merge_head_either h_pareto₁ h_pareto₂ <;> {
            rename_i h'
            rw [← List.get_zero_eq_head, List.get_of_eq] at h' 
            case h => exact h
            . simp at h'
              subst h' 
              simp
          }
            
    case tail h' =>
      cases ms₁ 
      case nil => 
        simp [merge] at h
        subst h 
        simp
        right
        assumption
      case cons m₁ ms₁ => 
        cases ms₂
        case nil => 
          simp [merge] at h
          let ⟨h₁, h₂⟩ := h 
          subst h₁ h₂
          simp 
          right
          assumption
        case cons m₂ ms₂ => 
          cases four_cases F m₁ m₂
          case first_dom h_dom => 
            let ⟨n, h'⟩ := merge_first_dom ms₁ h_pareto₂ h_dom
            simp [h'] at h
            let ⟨h₁, h₂⟩ := h
            subst h₁ h₂
            cases @ih ms₁ (ms₂.drop n) (pareto_rest h_pareto₁)
              (pareto_drop _ (pareto_rest h_pareto₂)) (by simp) h' 
            case inl => 
              left 
              apply List.Mem.tail
              assumption
            case inr => 
              right 
              apply List.Mem.tail
              apply List.mem_of_mem_drop
              assumption

          case second_dom h_non_dom h_dom =>
            let ⟨n, h'⟩ := merge_second_dom ms₂ h_pareto₁ h_dom h_non_dom
            simp [h'] at h
            let ⟨h₁, h₂⟩ := h
            subst h₁ h₂
            cases @ih (ms₁.drop n) ms₂ (pareto_drop _ (pareto_rest h_pareto₁))
              (pareto_rest h_pareto₂) (by simp) h' 
            case inl => 
              left
              apply List.Mem.tail
              apply List.mem_of_mem_drop
              assumption
            case inr => 
              right 
              apply List.Mem.tail
              assumption
              
          case first_lw h_non_dom₁ h_non_dom₂ h_lw => 
            simp [merge, *] at h
            cases ih (pareto_rest h_pareto₁) h_pareto₂ (by simp [h]) h'
            case inl => 
              left 
              apply List.Mem.tail
              assumption
            case inr => 
              right
              assumption

          case second_lw => 
            have : ¬ m₁.lw > m₂.lw := by {
              simp
              apply Nat.le_of_lt
              assumption
            }
            simp [merge, *] at h
            cases ih h_pareto₁ (pareto_rest h_pareto₂) (by simp [h]) h'
            case inl => 
              left               
              assumption
            case inr => 
              right
              apply List.Mem.tail
              assumption
}

lemma merge_dom₁ (h_pareto₁ : pareto F ms₁) 
    (h_pareto₂ : pareto F ms₂) (h : m ∈ ms₁) : ∃ m_better, m_better ∈ merge F ⟨ms₁, ms₂⟩ ∧ dominates F m_better m := by {
  generalize h_merge : merge _ _ = rms
  induction rms generalizing ms₁ ms₂
  case nil => 
    cases ms₁ 
    case nil => 
      simp at h
    case cons m₁ ms₁ => 
      have : merge F (m₁ :: ms₁, ms₂) ≠ [] := by {
        apply merge_not_empty
        simp
      }
      contradiction
  case cons hd tl ih =>
    dwi { cases ms₁ } 
    case cons m₁ ms₁ => 
      cases ms₂
      case nil => 
        exists m 
        simp [dominates_refl]
        cases h 
        case head => 
          simp [merge] at h_merge
          simp [h_merge]
        case tail h => 
          right
          simp [merge] at h_merge
          simp [h_merge] at h
          assumption
      case cons m₂ ms₂ => 
        cases four_cases F m₁ m₂
        case first_dom h_dom => 
          let ⟨n, h'⟩ := merge_first_dom ms₁ h_pareto₂ h_dom
          simp [h_merge] at h'
          cases h 
          case head => 
            exists m
            simp [dominates_refl, h']
          case tail h => 
            let ⟨h_better, ih⟩ := @ih ms₁ (ms₂.drop n) (pareto_rest h_pareto₁) (pareto_drop _ (pareto_rest h_pareto₂)) h (by simp [h'])
            exists h_better 
            simp [ih]
        case second_dom h_non_dom h_dom =>
          let ⟨n, ⟨h_left, h_right⟩⟩ := merge_second_dom ms₂ h_pareto₁ h_dom h_non_dom
          simp [h_merge] at h_left
          cases h 
          case head => 
            exists m₂ 
            simp [h_left, h_dom]
          case tail h => 
            replace h := (by exact h : m ∈ ms₁)
            have h_take_drop : ms₁ = ms₁.take n ++ ms₁.drop n := by simp 
            rw [h_take_drop, List.mem_append] at h
            cases h
            case inl h => 
              exists m₂ 
              simp [h_left]
              exact h_right _ h
            case inr h_mem => 
              let ⟨h_better, ⟨h₁, h₂⟩⟩ := ih (pareto_drop _ (pareto_rest h_pareto₁)) (pareto_rest h_pareto₂) h_mem (by simp [h_left])
              exists h_better
              dwi { constructor } 
              case left => 
                apply List.Mem.tail
                assumption
        case first_lw h_non_dom₁ h_non_dom₂ h_lw =>
          simp [merge, *] at h_merge
          cases h 
          case head => 
            exists m  
            simp [dominates_refl, *]
          case tail h_mem => 
            let ⟨m_better, h⟩ := ih (pareto_rest h_pareto₁) h_pareto₂ h_mem (by simp [h_merge])
            exists m_better
            simp [h]
        case second_lw h_lw => 
          replace h_lw := Nat.not_lt_of_lt h_lw
          simp [merge, *] at h_merge
          let ⟨m_better, h⟩ := ih h_pareto₁ (pareto_rest h_pareto₂) h (by simp [h_merge])
          exists m_better
          simp [h]      
    }

lemma merge_dom₂ (h_pareto₁ : pareto F ms₁) 
    (h_pareto₂ : pareto F ms₂) (h : m ∈ ms₂) : ∃ m_better, m_better ∈ merge F ⟨ms₁, ms₂⟩ ∧ dominates F m_better m := by {
  generalize h_merge : merge _ _ = rms
  induction rms generalizing ms₁ ms₂
  case nil => 
    cases ms₁ 
    case nil => 
      simp [merge] at h_merge 
      subst h_merge
      simp at h
    case cons m₁ ms₁ => 
      have : merge F (m₁ :: ms₁, ms₂) ≠ [] := by {
        apply merge_not_empty
        simp
      }
      contradiction
  case cons hd tl ih =>
    cases ms₁ 
    case nil => 
      simp [merge] at h_merge 
      subst h_merge 
      exists m 
      simp only [h, dominates_refl]
    case cons m₁ ms₁ => 
      cases ms₂
      case nil => simp at h
      case cons m₂ ms₂ => 
        cases four_cases F m₁ m₂
        case first_dom h_dom => 
          let ⟨n, ⟨h_left, h_right⟩⟩ := merge_first_dom ms₁ h_pareto₂ h_dom
          simp [h_merge] at h_left
          cases h 
          case head => 
            exists m₁
            simp [h_dom, h_left]
          case tail h => 
            replace h := (by exact h : m ∈ ms₂)
            have h_take_drop : ms₂ = ms₂.take n ++ ms₂.drop n := by simp 
            rw [h_take_drop, List.mem_append] at h
            cases h 
            case inl h => 
              exists m₁
              simp [h_left, h_right _ h]
            case inr h_mem => 
              let ⟨h_better, ⟨h₁, h₂⟩⟩ := ih (pareto_rest h_pareto₁) (pareto_drop _ (pareto_rest h_pareto₂)) h_mem (by simp [h_left])
              exists h_better
              dwi { constructor } 
              case left => 
                apply List.Mem.tail
                assumption
        case second_dom h_non_dom h_dom =>
          let ⟨n, h'⟩ := merge_second_dom ms₂ h_pareto₁ h_dom h_non_dom
          simp [h_merge] at h'
          cases h 
          case head => 
            exists m 
            simp [h', h_dom, dominates_refl]
          case tail h => 
            let ⟨h_better, ih⟩ := @ih (ms₁.drop n) ms₂ (pareto_drop _ (pareto_rest h_pareto₁)) (pareto_rest h_pareto₂) h (by simp [h'])
            exists h_better 
            simp [ih]
        case first_lw h_non_dom₁ h_non_dom₂ h_lw =>
          simp [merge, *] at h_merge
          let ⟨m_better, h⟩ := ih (pareto_rest h_pareto₁) h_pareto₂ h (by simp [h_merge])
          exists m_better
          simp [h]
        case second_lw h_lw => 
          replace h_lw := Nat.not_lt_of_lt h_lw
          simp [merge, *] at h_merge
          cases h 
          case head => 
            exists m
            simp [dominates_refl, *]
          case tail h_mem => 
            let ⟨h_better, h⟩ := ih h_pareto₁ (pareto_rest h_pareto₂) h_mem (by simp [h_merge])
            exists h_better
            simp [h]
    }