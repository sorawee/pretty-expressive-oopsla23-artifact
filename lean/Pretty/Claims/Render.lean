import Pretty.Defs.Basic
import Pretty.Tactic

/-!
## Theorems about the rendering relation ($⇓_\mathcal{R}$)
-/

/--
Determinism of the rendering relation (Section 3.3)
-/
theorem Render_deterministic (h₁ : Render d c i L₁) (h₂ : Render d c i L₂) : L₁ = L₂ := by 
  induction h₁ generalizing L₂
  case text | nl => 
    dwi { cases h₂ }
  case nest ih => 
    cases h₂
    case nest h => exact ih h
  case align ih => 
    cases h₂
    case align h => exact ih h
  case reset ih => 
    cases h₂
    case reset h => exact ih h
  case concat_single_single ih₁ ih₂ => 
    cases h₂
    case concat_single_single h₁ h₂ => 
      cases ih₁ h₁
      cases ih₂ h₂
      rfl
    case concat_single_multi h₁ h₂ => 
      cases ih₁ h₁
      cases ih₂ h₂
    case concat_multi_single h | concat_multi_multi h => 
      cases ih₁ h
  case concat_single_multi ih₁ ih₂ => 
    cases h₂
    case concat_single_single h₁ h₂ => 
      cases ih₁ h₁
      cases ih₂ h₂
    case concat_single_multi h₁ h₂ => 
      cases ih₁ h₁
      cases ih₂ h₂
      rfl
    case concat_multi_single h | concat_multi_multi h => 
      cases ih₁ h
  case concat_multi_single ih₁ ih₂ =>
    cases h₂
    case concat_single_single h₁ _ | concat_single_multi h₁ _ => 
      cases ih₁ h₁
    case concat_multi_single h₂ h₁ => 
      cases ih₁ h₁
      cases ih₂ h₂
      rfl
    case concat_multi_multi h₂ h₁ => 
      cases ih₁ h₁
      cases ih₂ h₂
  case concat_multi_multi ih₁ ih₂ =>
    cases h₂
    case concat_single_single h₁ _ | concat_single_multi h₁ _ => 
      cases ih₁ h₁
    case concat_multi_single h₂ h₁ => 
      cases ih₁ h₁
      cases ih₂ h₂
    case concat_multi_multi h₂ h₁ => 
      cases ih₁ h₁
      cases ih₂ h₂
      rfl

/--
Totality of the rendering relation (Section 3.3)
-/
theorem Render_total (c i : ℕ) (h : Choiceless d) : ∃ L, Render d c i L := by 
  dwi { induction d generalizing c i }
  case text s => 
    exists (Layout.single s)
    constructor
  case nl => 
    exists Layout.multi "" [] ⟨i, ""⟩
    constructor
  case concat ih₁ ih₂ => 
    cases h
    case concat h₁ h₂ => 
      let ⟨L₁, h₁⟩ := @ih₁ c i h₁
      cases L₁
      case single s₁ => 
        let ⟨L₂, h₂⟩ := @ih₂ (c + s₁.length) i h₂
        cases L₂
        case single s₂ => 
          exists (Layout.single (s₁ ++ s₂))
          dwi { constructor }
        case multi first₂ middle₂ last₂ => 
          exists (Layout.multi (s₁ ++ first₂) middle₂ last₂)
          dwi { constructor }
      case multi first₁ middle₁ last₁_c => 
        let ⟨i_last₁, last₁⟩ := last₁_c
        let ⟨L₂, h₂⟩ := @ih₂ (i_last₁ + last₁.length) i h₂
        cases L₂
        case single s₂ => 
          exists Layout.multi first₁ middle₁ ⟨i_last₁, last₁ ++ s₂⟩
          dwi { constructor }
        case multi first₂ middle₂ last₂ =>
          exists (Layout.multi first₁ (middle₁ ++ [⟨i_last₁, last₁ ++ first₂⟩] ++ middle₂) last₂)
          dwi { constructor }
  case nest n _ ih => 
    cases h
    case nest h => 
      let ⟨L, _⟩ := @ih c (i + n) h
      exists L
      dwi { constructor }
  case align ih =>
    cases h
    case align h => 
      let ⟨L, _⟩ := @ih c c h
      exists L
      dwi { constructor }
  case reset ih => 
    cases h
    case reset h => 
      let ⟨L, _⟩ := @ih c 0 h
      exists L
      dwi { constructor }