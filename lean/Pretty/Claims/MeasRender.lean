import Pretty.Defs.Basic
import Pretty.Claims.Render
import Pretty.Supports.FactoryMath

/-!
## Theorems about the measure computation/rendering relation ($⇓_\mathbb{M}$)
-/

/--
Determinism of the measure computation relation (Section 5.3)
-/
theorem MeasRender_deterministic {F : Factory α} {m₁ m₂ : Meas}
  (h₁ : @MeasRender α F d c i m₁) (h₂ : @MeasRender α F d c i m₂) : m₁ = m₂ := by 
  induction h₁ generalizing m₂
  case text | nl => dwi { cases h₂ }
  case nest ih | align ih => 
    rename Doc => d
    cases h₂
    rename_i last₂ cost₂ x₂ y₂ h₂ 
    dwi { cases ih h₂ }
  case concat ihₗ ihᵣ => 
    cases h₂ 
    case concat h₂ h₁ h => 
      cases ihₗ h₁
      cases ihᵣ h₂
      simp [*]

/--
Correctness of the measure computation relation 
when it results in one line (first part of Theorem 5.3)
-/
theorem MeasRender_single_correct (F : Factory α) 
    (h_render : Render d c i (Layout.single s)) : 
    ∃ cost y, MeasRender F d c i ⟨c + s.length, cost, d, c + s.length, y⟩ := by
  induction d generalizing c i s
  case text => 
    exists F.text c s.length, i
    cases h_render 
    constructor
  case nl => exists F.text c s.length, i 
  case nest ih  => 
    cases h_render
    rename_i h  
    let ⟨cost, y, hh⟩ := ih h
    exists cost, y 
    constructor
    assumption
  case align ih => 
    cases h_render
    rename_i h  
    let ⟨cost, y, hh⟩ := ih h
    exists cost, (max i y) 
    constructor
    assumption
  case concat ih₁ ih₂ =>
    generalize h_layout : Layout.single s = L at h_render
    cases h_render
    case concat_single_single d₁ d₂ s₁ s₂ h₁ h₂ => 
      cases h_layout
      let ⟨cost₁, y₁, _⟩ := ih₁ h₁
      let ⟨cost₂, y₂, _⟩ := ih₂ h₂
      exists F.concat cost₁ cost₂, max y₁ y₂
      have h_ans : { last := c + String.length (s₁ ++ s₂), 
                     cost := F.concat cost₁ cost₂, 
                     doc := Doc.concat d₁ d₂,
                     x := c + String.length (s₁ ++ s₂), y := max y₁ y₂ } = 
       Meas.concat F 
         { last := c + String.length s₁, 
           cost := cost₁, 
           doc := d₁, x := c + String.length s₁,
           y := y₁ } 
         { last := c + String.length s₁ + String.length s₂, 
           cost := cost₂,
           doc := d₂, 
           x := c + String.length s₁ + String.length s₂, 
           y := y₂ } := by 
        simp_arith [Meas.concat]
      dwi { constructor }
    case concat_single_multi | concat_multi_single | concat_multi_multi => 
      injection h_layout 
  case choice =>
    cases h_render

/--
Correctness of the measure computation relation 
when it results in multiple lines (second part of Theorem 5.3)
-/
theorem MeasRender_multi_correct (F : Factory α) 
    (h_render : Render d c i (Layout.multi first middle last))  : 
    ∃ cost y, MeasRender F d c i ⟨last.length,
                                  cost, d, 
                                  (Layout.multi first middle last).max_with_offset c, y⟩ := by
  induction d generalizing c i first middle last
  case text => cases h_render 
  case nl =>
    exists F.nl i, i
    cases h_render 
    simp [String.length, List.asString, Layout.max_with_offset]
    constructor
  case nest ih  => 
    cases h_render
    rename_i h
    let ⟨cost, ⟨y, _⟩⟩ := ih h
    exists cost, y
    constructor
    assumption
  case align ih => 
    cases h_render
    rename_i h
    let ⟨cost, ⟨y, _⟩⟩ := ih h
    exists cost, (max i y)
    constructor
    assumption
  case choice => cases h_render 
  case concat ih₁ ih₂ => 
    cases h_render 
    case concat_single_multi s first h₁ h₂ => 
      let ⟨cost₁, ⟨y₁, _⟩⟩ := MeasRender_single_correct F h₁
      let ⟨cost₂, ⟨y₂, _⟩⟩ := ih₂ h₂
      exists F.concat cost₁ cost₂, max y₁ y₂
      dwi { apply MeasRender.concat }
      case h => simp [Meas.concat, Layout.max_with_offset, add_assoc]
    case concat_multi_single last s h₂ h₁ =>
      let ⟨cost₁, ⟨y₁, _⟩⟩ := ih₁ h₁
      let ⟨cost₂, ⟨y₂, _⟩⟩ := MeasRender_single_correct F h₂
      exists F.concat cost₁ cost₂, max y₁ y₂
      dwi { apply MeasRender.concat }
      case h => 
        simp [Meas.concat, Layout.max_with_offset, max_assoc, max_comm]
    case concat_multi_multi middle₁ last₁ first₂ middle₂ h₁ h₂ =>
      let ⟨cost₁, ⟨y₁, _⟩⟩ := ih₁ h₁
      let ⟨cost₂, ⟨y₂, _⟩⟩ := ih₂ h₂
      exists F.concat cost₁ cost₂, max y₁ y₂
      dwi { apply MeasRender.concat }
      case h => 
        simp [Meas.concat, Layout.max_with_offset, max_assoc]
        congr 1
        generalize List.foldl max 0 (List.map String.length middle₁) = q₁
        generalize List.map String.length middle₂ = q₂
        generalize last.length = q₃
        generalize last₁.length + first₂.length = q₄
        rw [(by simp : max q₁ q₄ = max (max q₁ q₄) 0)]
        simp only [List.fold_max_max_eq_max_fold_max]
        generalize List.foldl max 0 q₂ = q₅
        rw [max_comm, max_assoc, max_assoc]
        simp [max_comm]

/--
Totality of the measure computation relation (Section 5.3)
-/
theorem MeasRender_total (F : Factory α) (d : Doc) (c i : ℕ) (h : Choiceless d) : 
    ∃ m, MeasRender F d c i m := by 
  let ⟨L, h⟩ := Render_total c i h
  cases L
  case single s => 
    let ⟨cost, ⟨y, _⟩⟩ := MeasRender_single_correct F h 
    exists ⟨c + s.length, cost, d, c + s.length, y⟩
  case multi first middle last => 
    let ⟨cost, ⟨y, _⟩⟩ := MeasRender_multi_correct F h
    exists ⟨last.length, cost, d, (Layout.multi first middle last).max_with_offset c, y⟩