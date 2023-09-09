import Pretty.Defs.Basic
import Pretty.Claims.Render
import Pretty.Supports.FactoryMath
import Pretty.Supports.LayoutCost

/-!
## Theorems about the measure computation/rendering relation ($⇓_\mathbb{M}$)
-/

/--
Determinism of the measure computation relation (Section 6.2)
-/
theorem MeasRender_deterministic {F : Factory α} {m₁ m₂ : Meas}
  (h₁ : @MeasRender α F d c i m₁) (h₂ : @MeasRender α F d c i m₂) : m₁ = m₂ := by 
  induction h₁ generalizing m₂
  case text | nl => dwi { cases h₂ }
  case nest ih | align ih | reset ih => 
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
when it results in one line (first part of Theorem 6.2)
-/
theorem MeasRender_single_correct (F : Factory α) 
    (h_layout : Layout.single s = L)
    (h_render : Render d c i L) : 
    ∃ y, MeasRender F d c i ⟨c + s.length, L.find_cost F c, d, c + s.length, y⟩ := by
  subst h_layout
  induction d generalizing c i s
  case text => 
    exists i
    cases h_render 
    constructor
  case nl => exists i 
  case nest ih  => 
    cases h_render
    rename_i h  
    let ⟨y, hh⟩ := ih h
    exists y 
    constructor
    assumption
  case align ih | reset ih => 
    cases h_render
    rename_i h  
    let ⟨y, hh⟩ := ih h
    exists max i y
    constructor
    assumption
  case concat ih₁ ih₂ =>
    generalize h_layout : Layout.single s = L at h_render
    cases h_render
    case concat_single_single d₁ d₂ s₁ s₂ h₁ h₂ => 
      cases h_layout
      let ⟨y₁, _⟩ := ih₁ h₁
      let ⟨y₂, _⟩ := ih₂ h₂
      exists max y₁ y₂
      have h_ans : { last := c + String.length (s₁ ++ s₂), 
                     cost := (Layout.single (s₁ ++ s₂)).find_cost F c, 
                     doc := Doc.concat d₁ d₂,
                     x := c + String.length (s₁ ++ s₂), y := max y₁ y₂ } = 
       Meas.concat F 
         { last := c + String.length s₁, 
           cost := (Layout.single s₁).find_cost F c, 
           doc := d₁, x := c + String.length s₁,
           y := y₁ } 
         { last := c + String.length s₁ + String.length s₂, 
           cost := (Layout.single s₂).find_cost F (c + String.length s₁),
           doc := d₂, 
           x := c + String.length s₁ + String.length s₂, 
           y := y₂ } := by 
        simp_arith [Meas.concat, Layout.find_cost, Factory.text_concat]
      dwi { constructor }
    case concat_single_multi | concat_multi_single | concat_multi_multi => 
      injection h_layout 
  case choice => cases h_render

/--
Correctness of the measure computation relation 
when it results in multiple lines (second part of Theorem 6.2)
-/
theorem MeasRender_multi_correct (F : Factory α) 
    (h_layout : Layout.multi first middle ⟨i_last, last⟩ = L)
    (h_render : Render d c i L)  : 
    ∃ y, MeasRender F d c i ⟨i_last + last.length,
                             L.find_cost F c, d, 
                             L.max_with_offset c, y⟩ := by
  subst h_layout
  induction d generalizing c i first middle last i_last
  case text => cases h_render 
  case nl =>
    exists i
    cases h_render 
    simp [String.length, List.asString, Layout.max_with_offset, Layout.find_cost, compute_cost, Factory.text_id_left, Factory.text_id_right]
    constructor
  case nest ih  => 
    cases h_render
    rename_i h
    let ⟨y, _⟩ := ih h
    exists y
    constructor
    assumption
  case align ih | reset ih => 
    cases h_render
    rename_i h
    let ⟨y, _⟩ := ih h
    exists max i y
    constructor
    assumption
  case choice => cases h_render 
  case concat ih₁ ih₂ => 
    cases h_render 
    case concat_single_multi s first h₁ h₂ => 
      generalize h_layout : Layout.single s = L at h₁
      let ⟨y₁, _⟩ := MeasRender_single_correct F h_layout h₁
      subst h_layout
      let ⟨y₂, _⟩ := ih₂ h₂
      exists max y₁ y₂
      dwi { apply MeasRender.concat }
      case h => 
        simp [Meas.concat, Layout.max_with_offset, add_assoc, Layout.find_cost]
        rw [compute_cost_extract]
        conv => 
          right 
          rw [compute_cost_extract]
        simp [← Factory.concat_assoc, Factory.text_concat]
    case concat_multi_single last s h₂ h₁ =>
      let ⟨y₁, _⟩ := ih₁ h₁
      generalize h_layout : Layout.single s = L at h₂
      let ⟨y₂, _⟩ := MeasRender_single_correct F h_layout h₂
      subst h_layout
      exists max y₁ y₂
      dwi { apply MeasRender.concat }
      case h => 
        simp [Meas.concat, Layout.max_with_offset, add_assoc]
        rw [max_assoc]
        simp [max_comm, ← max_assoc, ← add_assoc]
        simp [Layout.find_cost, compute_cost_split, compute_cost, Factory.concat_assoc, Factory.text_concat]
    case concat_multi_multi middle₁ i_last₁ last₁ first₂ middle₂ h₁ h₂ =>
      let ⟨y₁, _⟩ := ih₁ h₁
      let ⟨y₂, _⟩ := ih₂ h₂
      exists max y₁ y₂
      dwi { apply MeasRender.concat }
      case h => 
        simp [Meas.concat, Layout.max_with_offset, max_assoc]
        congr 1
        generalize List.foldl max 0 (List.map (fun ⟨i_line, line⟩ => i_line + String.length line) middle₁) = q₁
        generalize List.map (fun ⟨i_line, line⟩ => i_line + String.length line) middle₂ = q₂
        generalize i_last + last.length = q₃
        rw [add_assoc]
        generalize i_last₁ + (last₁.length + first₂.length) = q₄
        rw [(by simp : max q₁ q₄ = max (max q₁ q₄) 0)]
        simp only [List.fold_max_max_eq_max_fold_max]
        generalize List.foldl max 0 q₂ = q₅
        constructor 
        case right => 
          conv => 
            left
            arg 2
            rw [max_comm, max_assoc, max_assoc]
          simp [max_comm]
        case left => 
          simp [Layout.find_cost, compute_cost_split, compute_cost, Factory.text_id_left, ← Factory.text_concat, Factory.concat_assoc]

/--
Totality of the measure computation relation (Section 6.2)
-/
theorem MeasRender_total (F : Factory α) (d : Doc) (c i : ℕ) (h : Choiceless d) : 
    ∃ m, MeasRender F d c i m := by 
  let ⟨L, h⟩ := Render_total c i h
  cases L
  case single s => 
    generalize h_layout : Layout.single s = L at h
    let ⟨y, _⟩ := MeasRender_single_correct F h_layout h 
    exists ⟨c + s.length, L.find_cost F c, d, c + s.length, y⟩
  case multi first middle last_c => 
    let ⟨i_last, last⟩ := last_c
    generalize h_layout : Layout.multi first middle ⟨i_last, last⟩ = L at h
    let ⟨y, _⟩ := MeasRender_multi_correct F h_layout h
    exists ⟨i_last + last.length, L.find_cost F c, d, L.max_with_offset c, y⟩