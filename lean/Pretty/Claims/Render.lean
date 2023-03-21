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
  case text => 
    dwi { cases h₂ }
  case nl => 
    dwi { cases h₂ }
  case nest ih => 
    cases h₂
    case nest h => exact ih h
  case align ih => 
    cases h₂
    case align h => exact ih h
  case concat_one ih₁ ih₂ => 
    cases h₂
    case concat_one h₁ h₂ => 
      cases ih₁ h₁
      cases ih₂ h₂
      rfl
    case concat_multi h₁ => 
      dwi { cases ih₁ h₁ }
  case concat_multi h_last₁ _ _ ih₁ ih₂ => 
    cases h₂
    case concat_one h₁ _ => 
      dwi { cases ih₁ h₁ }
    case concat_multi h_last₂ h₂ h₁ => 
      cases ih₁ h₁
      subst h_last₁ h_last₂
      cases ih₂ h₂
      rfl

/--
Totality of the rendering relation (Section 3.3)
-/
theorem Render_total (c i : ℕ) (h : Choiceless d) : ∃ L, Render d c i L := by 
  dwi { induction d generalizing c i }
  case text s => 
    exists ⟨s, []⟩
    constructor
  case nl => 
    exists ⟨"", [List.asString (List.replicate i ' ')]⟩
    constructor
  case concat ih₁ ih₂ => 
    cases h
    case concat h₁ h₂ => 
      let ⟨⟨s, ss⟩, h₁⟩ := @ih₁ c i h₁
      cases ss
      case nil => 
        let ⟨L₂, _⟩ := @ih₂ (c + s.length) i h₂
        exists ⟨s ++ L₂.fst, L₂.rst⟩
        dwi { constructor }
      case cons hd tl => 
        let ⟨L₂, _⟩ := @ih₂ (List.getLast (hd :: tl) (by simp)).length i h₂
        exists ⟨s, (List.dropLast (hd :: tl)) ++ [List.getLast (hd :: tl) (by simp) ++ L₂.fst] ++ L₂.rst⟩
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