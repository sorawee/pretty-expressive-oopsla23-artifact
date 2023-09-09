import Pretty.Supports.DocSize
import Pretty.Defs.Resolve
import Pretty.Claims.MeasRender

/-!
## Determinism of resolving theorems
-/

mutual 
  /--
  The determinism of resolving (Section 6.5)
  -/
  theorem Resolve_deterministic (h₁ : Resolve F d c i ms₁) (h₂ : Resolve F d c i ms₂) : ms₁ = ms₂ := by {
    match d with 
    | Doc.text _ => 
      cases h₁ 
      case text_taint h_bad h₁ => 
        cases h₂ 
        case text_taint h₂ => 
          have := MeasRender_deterministic h₁ h₂
          subst this
          simp
        case text_set h_c h_i _=> 
          cases h_bad 
          case inl h_bad => 
            replace h_bad := Nat.not_le_of_lt h_bad 
            contradiction
          case inr h_bad =>
            replace h_bad := Nat.not_le_of_lt h_bad 
            contradiction
      case text_set h_c h_i h₁ => 
        cases h₂ 
        case text_taint h_bad _ => 
          cases h_bad 
          case inl h_bad => 
            replace h_bad := Nat.not_le_of_lt h_bad 
            contradiction
          case inr h_bad =>
            replace h_bad := Nat.not_le_of_lt h_bad 
            contradiction
        case text_set h₂ => 
          have := MeasRender_deterministic h₁ h₂
          subst this
          simp
    | Doc.nl => 
      cases h₁ 
      case line_taint h_bad h₁ => 
        cases h₂ 
        case line_taint h₂ => 
          have := MeasRender_deterministic h₁ h₂
          subst this
          simp
        case line_set h_c h_i _ => 
          cases h_bad 
          case inl h_bad => 
            replace h_bad := Nat.not_le_of_lt h_bad 
            contradiction
          case inr h_bad =>
            replace h_bad := Nat.not_le_of_lt h_bad 
            contradiction
      case line_set h_c h_i h₁ => 
        cases h₂ 
        case line_taint h_bad _ => 
          cases h_bad 
          case inl h_bad => 
            replace h_bad := Nat.not_le_of_lt h_bad 
            contradiction
          case inr h_bad =>
            replace h_bad := Nat.not_le_of_lt h_bad 
            contradiction
        case line_set h₂ => 
          have := MeasRender_deterministic h₁ h₂
          subst this
          simp
    | Doc.nest n d' => 
      cases h₁
      case nest h₁ => 
        cases h₂ 
        case nest h₂ => 
          have := Resolve_deterministic h₁ h₂
          subst this 
          simp
    | Doc.align d' => 
      cases h₁ 
      case align h₁ h_ok =>
        cases h₂ 
        case align_taint h_bad => 
          replace h_bad := Nat.not_le_of_lt h_bad
          contradiction
        case align h₂ _ => simp [Resolve_deterministic h₁ h₂]
      case align_taint h h_bad => 
        cases h₂ 
        case align_taint h' _ => simp [Resolve_deterministic h h'] 
        case align => 
          replace h_bad := Nat.not_le_of_lt h_bad
          contradiction
    | Doc.reset d' => 
      cases h₁ 
      case reset h₁ h_ok =>
        cases h₂ 
        case reset_taint h_bad => 
          replace h_bad := Nat.not_le_of_lt h_bad
          contradiction
        case reset h₂ _ => simp [Resolve_deterministic h₁ h₂]
      case reset_taint h h_bad => 
        cases h₂ 
        case reset_taint h' _ => simp [Resolve_deterministic h h'] 
        case reset => 
          replace h_bad := Nat.not_le_of_lt h_bad
          contradiction
    | Doc.choice d₁ d₂ => 
      cases h₁
      case choice h_right h_left => 
        cases h₂ 
        case choice h_right' h_left' => 
          simp [Resolve_deterministic h_left h_left', Resolve_deterministic h_right h_right']
    | Doc.concat d₁ d₂ => 
      cases h₁ 
      case concat_taint h_taint₁ h_right₁ h_left₁ => 
        cases h₂
        case concat_taint h_taint₂ h_right₂ h_left₂ => 
          cases Resolve_deterministic h_left₁ h_left₂
          cases Resolve_deterministic h_right₁ h_right₂
          simp [h_taint₁] at h_taint₂
          simp [*]
        case concat_set h_left₂ _ => cases Resolve_deterministic h_left₁ h_left₂
      case concat_set h_left₁ h_right₁ =>
        cases h₂ 
        case concat_taint h_taint₂ h_right₂ h_left₂ => cases Resolve_deterministic h_left₁ h_left₂
        case concat_set h_left₂ h_right₂ => 
          cases Resolve_deterministic h_left₁ h_left₂
          cases ResolveConcat_deterministic h_right₁ h_right₂ 
          simp         
  }

  theorem ResolveConcatOne_deterministic 
      (h₁ : ResolveConcatOne F d m i msr₁)
      (h₂ : ResolveConcatOne F d m i msr₂) : 
      msr₁ = msr₂ := by
    cases h₁
    case tainted h₁ => 
      cases h₂
      case tainted h₂ => 
        cases Resolve_deterministic h₁ h₂
        simp
      case set h₂ => cases Resolve_deterministic h₁ h₂
    case set h₁ => 
      cases h₂
      case tainted h₂ => cases Resolve_deterministic h₁ h₂
      case set h₂ => 
        cases Resolve_deterministic h₁ h₂
        simp

  theorem ResolveConcat_deterministic {ms : List Meas}
      (h₁ : ResolveConcat F ms d i msr₁)
      (h₂ : ResolveConcat F ms d i msr₂) : 
      msr₁ = msr₂ := by
    cases h₁ 
    case one => 
      dwi { cases h₂ }
      case one => apply ResolveConcatOne_deterministic <;> assumption
    case cons h_rest₁ h_current₁ => 
      dwi { cases h₂ } 
      case cons h_current₂ h_rest₂ => 
        cases ResolveConcatOne_deterministic h_current₁ h_current₂
        cases ResolveConcat_deterministic h_rest₁ h_rest₂
        simp
end
termination_by 
  ResolveConcatOne_deterministic => (d.size, 1, 0)
  ResolveConcat_deterministic => (d.size, 2, ms.length)
  Resolve_deterministic => (d.size, 0, 0)