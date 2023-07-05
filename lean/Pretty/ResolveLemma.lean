import Pretty.ResolveDef
import Pretty.MeasRenderThm
import Pretty.ParetoThm

lemma bad_taint_mode_always_tainted 
  (h : Resolve F d c i ms) 
  (h_bad : c > F.W ∨ i > F.W) : ∃ m, ms = MeasureSet.tainted m := by 
  induction d generalizing c i ms
  case text => 
    cases h 
    case text_taint m _ _ => exists m 
    case text_set h_c h_i _ => 
      cases h_bad 
      case inl h_bad => 
        have : c ≤ F.W := by linarith
        replace h_bad := Nat.not_le_of_lt h_bad
        contradiction
      case inr h_bad => 
        replace h_bad := Nat.not_le_of_lt h_bad
        contradiction
  case nl => 
    cases h 
    case line_taint m _ _ => exists m
    case line_set h_c h_i _ => 
      cases h_bad 
      case inl h_bad => 
        replace h_bad := Nat.not_le_of_lt h_bad
        contradiction
      case inr h_bad => 
        replace h_bad := Nat.not_le_of_lt h_bad
        contradiction
  case nest n _ ih => 
    cases h
    case nest h => 
      cases h_bad 
      case inl h_bad => 
        let ⟨m, _⟩ := ih h (by {
          left
          linarith
        })
        exists m.adjust_nest n
        simp [*, MeasureSet.lift, Meas.adjust_nest]
      case inr h_bad => 
        let ⟨m, _⟩ := ih h (by {
          right
          linarith
        })
        exists m.adjust_nest n
        simp [*, MeasureSet.lift, Meas.adjust_nest]
  case align ih => 
    cases h
    case align h _ => 
      cases h_bad 
      case inl h_bad => 
        let ⟨m, _⟩ := ih h (by {
          left
          linarith
        })
        exists m.adjust_align i
        simp [*, MeasureSet.lift, Meas.adjust_align]
      case inr => linarith
    case align_taint ms h _ => 
      cases ms 
      case tainted m => exists m.adjust_align i
      case set ms _ => exists (ms.head (by assumption)).adjust_align i
  case choice ih₁ ih₂ => 
    cases h 
    case choice h_left h_right => 
      let ⟨m, h⟩ := ih₁ h_left h_bad
      let ⟨m', h'⟩ := ih₂ h_right h_bad
      exists m 
      subst h h'
      simp [*, MeasureSet.union]
  case concat ih₁ _ => 
    cases h 
    case concat_taint m₁ _ m₂ _ _ _ => 
      exists (Meas.concat F m₁ m₂)
    case concat_set h_left _ => 
      let ⟨_, _⟩ := ih₁ h_left h_bad 
      contradiction