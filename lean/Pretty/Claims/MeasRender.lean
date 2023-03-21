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
    (h_render : Render d c i ⟨s, []⟩) : 
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
    generalize h_layout : Layout.mk s [] = L at h_render
    cases h_render
    case concat_one d₁ d₂ s₁ s₂ _ h₁ h₂ => 
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
    case concat_multi => 
      injection h_layout 
      simp at *
  case choice =>
    cases h_render

/--
Correctness of the measure computation relation 
when it results in multiple lines (second part of Theorem 5.3)
-/
theorem MeasRender_multi_correct (F : Factory α) 
    (h_render : Render d c i ⟨s, ss⟩) (h_non_empty : ss ≠ []) : 
    ∃ cost y, MeasRender F d c i ⟨(List.getLast ss h_non_empty).length,
                                  cost, d, 
                                  Layout.max_with_offset c ⟨s, ss⟩, y⟩ := by
  induction d generalizing c i s ss
  case text => 
    cases h_render 
    simp at h_non_empty
  case nl =>
    exists F.nl i, i
    cases h_render 
    simp only [
      String.length, List.asString, ne_eq, List.getLast_singleton',
      List.length_replicate, Layout.max_with_offset, List.length_nil,
      add_zero, List.foldl, ge_iff_le, nonpos_iff_eq_zero, zero_le,
      max_eq_right
    ]
    constructor    
  case nest ih  => 
    cases h_render
    rename_i h
    let ⟨cost, ⟨y, _⟩⟩ := ih h h_non_empty
    exists cost, y
    constructor
    assumption
  case align ih => 
    cases h_render
    rename_i h
    let ⟨cost, ⟨y, _⟩⟩ := ih h h_non_empty
    exists cost, (max i y)
    constructor
    assumption
  case choice => cases h_render 
  case concat ih₁ ih₂ => 
    cases h_render 
    case concat_one s t h₁ h₂ => 
      let ⟨cost₁, ⟨y₁, _⟩⟩ := MeasRender_single_correct F h₁
      let ⟨cost₂, ⟨y₂, _⟩⟩ := ih₂ h₂ h_non_empty
      exists F.concat cost₁ cost₂, max y₁ y₂
      have h_x : Layout.max_with_offset c ⟨s ++ t, ss⟩ = 
          max (c + s.length) (Layout.max_with_offset (c + s.length) ⟨t, ss⟩) := by {
        simp [Layout.max_with_offset, String.length, String.append, Nat.add_assoc]
      }
      rw [h_x]
      dwi { apply MeasRender.concat }
    case concat_multi ss slast t ts _ h_last h₂ h₁ => 
      let ⟨cost₁, ⟨y₁, _⟩⟩ := ih₁ h₁ (by assumption)
      have h_droplast : List.map String.length ss = 
          List.map String.length 
                   (List.dropLast ss ++ [List.getLast ss (by assumption)]) := by
        simp [List.dropLast_append_getLast]
      cases ts
      case nil => 
        let ⟨cost₂, ⟨y₂, _⟩⟩ := MeasRender_single_correct F h₂
        exists F.concat cost₁ cost₂, max y₁ y₂
        have h_x : Layout.max_with_offset c ⟨s, List.dropLast ss ++ [slast ++ t] ++ []⟩ = 
            max (Layout.max_with_offset c ⟨s, ss⟩) (slast.length + t.length) := by {
          simp [Layout.max_with_offset]
          rw [h_droplast, List.map_append, List.foldl_append]
          subst h_last
          simp [max_assoc]
        }
        rw [h_x]
        dwi { apply MeasRender.concat }
        case h₂ => subst h_last; simpa 
        case h => simp [Meas.concat, *]
            
      case cons hd tl => 
        let ⟨cost₂, ⟨y₂, _⟩⟩ := ih₂ h₂ (by simp)
        exists F.concat cost₁ cost₂, max y₁ y₂
        have h_x : Layout.max_with_offset c ⟨s, List.dropLast ss ++ [slast ++ t] ++ hd :: tl⟩ = 
            max (Layout.max_with_offset c ⟨s, ss⟩) 
                (Layout.max_with_offset slast.length ⟨t, hd :: tl⟩) := by {
          simp only [
            Layout.max_with_offset, List.append_assoc, List.singleton_append,
            List.map_append, List.map, String.length_append, List.foldl_append,
            List.foldl, ge_iff_le, le_max_iff, max_le_iff, nonpos_iff_eq_zero, 
            zero_le, max_eq_right
          ]
          rw [h_droplast, List.map_append, List.foldl_append]
          subst h_last
          simp only [
            ge_iff_le, le_max_iff, max_le_iff, max_assoc, List.foldl, 
            add_le_iff_nonpos_right, nonpos_iff_eq_zero, le_add_iff_nonneg_right,
            zero_le, and_true, true_or, max_eq_right
          ]
          dwi { apply congr }
          case h₂ => simp [List.fold_max_max_eq_max_fold_max]
        }
        rw [h_x]
        dwi { constructor }
        case h₂ => 
          subst h_last
          simpa [List.getLast_append']
        case h => simp_arith [Meas.concat, *, List.getLast_append']

/--
Totality of the measure computation relation (Section 5.3)
-/
theorem MeasRender_total (F : Factory α) (d : Doc) (c i : ℕ) (h : Choiceless d) : 
    ∃ m, MeasRender F d c i m := by 
  let ⟨⟨s, ss⟩, h⟩ := Render_total c i h
  cases ss 
  case nil => 
    let ⟨cost, ⟨y, _⟩⟩ := MeasRender_single_correct F h 
    exists ⟨c + s.length, cost, d, c + s.length, y⟩
  case cons hd tl => 
    let ⟨cost, ⟨y, _⟩⟩ := MeasRender_multi_correct F h (by simp)
    exists ⟨(List.getLast (hd :: tl) (by simp)).length, cost, 
            d, Layout.max_with_offset c (Layout.mk s (hd :: tl)), y⟩