import Pretty.Defs.Basic
import Pretty.Tactic

/-!
## Theorems about the widening relation
-/

/--
Determinism of the widening relation (Section 3.3)
-/
theorem Widen_deterministic (h₁ : Widen d L₁) (h₂ : Widen d L₂) : L₁ = L₂ := by 
  induction d generalizing L₁ L₂
  case text | nl => 
    cases h₁ 
    cases h₂
    simp
  case nest ih | align ih => 
    cases h₁ 
    rename_i h₁ 
    cases h₂
    rename_i h₂ 
    simp [ih h₁ h₂]
  case choice ih_left ih_right | concat ih_left ih_right =>
    cases h₁ 
    rename_i h_left₁ h_right₁
    cases h₂
    rename_i h_left₂ h_right₂
    simp [ih_left h_left₁ h_left₂, ih_right h_right₁ h_right₂]

/--
Totality of the widening relation (Section 3.3)
-/
theorem Widen_total : ∃ L, Widen d L := by 
  induction d
  case text s => 
    exists [Doc.text s]
    constructor
  case nl => 
    exists [Doc.nl]
    constructor
  case nest n _ ih => 
    let ⟨L, h⟩ := ih
    exists L.map (fun d => Doc.nest n d)
    constructor
    assumption
  case align ih => 
    let ⟨L, h⟩ := ih
    exists L.map (fun d => Doc.align d)
    constructor
    assumption
  case choice ih₁ ih₂ => 
    let ⟨L₁, h₁⟩ := ih₁
    let ⟨L₂, h₂⟩ := ih₂
    exists (L₁ ++ L₂)
    dwi { constructor }
  case concat ih₁ ih₂ => 
    let ⟨L₁, h₁⟩ := ih₁
    let ⟨L₂, h₂⟩ := ih₂
    exists (L₁.map (fun d₁ => L₂.map (fun d₂ => Doc.concat d₁ d₂))).join
    dwi { constructor }

/--
Choicelessness of widened documents (not stated in the paper)
-/
-- This lemma can be made more general by not requiring `d` to be supplied,
-- but this current form suffices for our purposes.
lemma Widen_choiceless (h : Widen d D) (h_in : d_choiceless ∈ D) : Choiceless d_choiceless := by 
  induction d generalizing D d_choiceless
  case text | nl => 
    cases h 
    cases List.eq_of_mem_singleton h_in
    constructor 
  case nest ih | align ih => 
    cases h 
    rw [List.mem_map] at h_in
    let ⟨_, _, h_right⟩ := h_in
    subst h_right 
    constructor 
    dwi { apply ih }
  case choice ih₁ ih₂ => 
    cases h 
    rw [List.mem_append] at h_in
    cases h_in <;> [apply ih₁; apply ih₂] <;> assumption 
  case concat ih₁ ih₂ => 
    cases h 
    case concat => 
      rw [List.mem_join] at h_in
      let ⟨_, h_left, h_right⟩ := h_in
      rw [List.mem_map] at h_left 
      let ⟨_, _, h_left_right⟩ := h_left 
      subst h_left_right
      rw [List.mem_map] at h_right 
      let ⟨_, _, h_right_right⟩ := h_right 
      subst h_right_right 
      constructor <;> [apply ih₁; apply ih₂] <;> assumption