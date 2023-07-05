import Pretty.ResolveDetThm
import Pretty.DocSizeLemma

/-!
Totality of resolving (Page 19, Section 5.6)
-/

mutual 
  theorem ResolveConcatOne_total (F : Factory α) (d : Doc) (m : Meas) (i : ℕ) : ∃ msr, ResolveConcatOne F d m i msr := by 
    let ⟨ms, h⟩ := Resolve_total F d m.lw i
    cases ms 
    case set ms h' =>
      exists MeasureSet.set (dedup F (ms.map (fun m' => Meas.concat F m m'))) (by {
        apply dedup_not_empty
        simp [h']
      })
      constructor <;> assumption
    case tainted m' => 
      exists MeasureSet.tainted (Meas.concat F m m')
      constructor
      assumption

  theorem ResolveConcat_total  (F : Factory α) (ms : List Meas) (d : Doc)
      (i : ℕ)
      (h_non_empty : ms ≠ []) : 
      ∃ msr, ResolveConcat F ms d i msr := by 
    match ms with 
    | [] => contradiction
    | [m] => 
      let ⟨msr, h⟩ := ResolveConcatOne_total F d m i
      exists msr 
      constructor
      assumption
    | m :: hd :: tl => 
      let ⟨msr, h⟩ := ResolveConcat_total F (hd :: tl) d i (by simp)
      let ⟨msr', h'⟩ := ResolveConcatOne_total F d m i 
      exists MeasureSet.union F msr' msr
      dwi { constructor }

  theorem Resolve_total (F : Factory α) (d : Doc) (c i : ℕ) : ∃ ms, Resolve F d c i ms := by 
    match d with
    | Doc.text s => 
      by_cases h_i : i ≤ F.W
      case pos => 
        by_cases h_c : c + s.length ≤ F.W 
        case pos => 
          let ⟨m, h⟩ := MeasRender_total F (Doc.text s) c i (by constructor)
          exists MeasureSet.set [m] (by simp) 
          constructor <;> assumption
        case neg => 
          replace h_c := Nat.gt_of_not_le h_c
          let ⟨m, h⟩ := MeasRender_total F (Doc.text s) c i (by constructor)
          exists MeasureSet.tainted m
          constructor 
          case h_bad => simp [h_c]
          case h => assumption
      case neg => 
        replace h_i := Nat.gt_of_not_le h_i
        let ⟨m, h⟩ := MeasRender_total F (Doc.text s) c i (by constructor)
        exists MeasureSet.tainted m
        constructor 
        case h_bad => simp [h_i]
        case h => assumption
    | Doc.nl =>
      by_cases h_i : i ≤ F.W
      case pos => 
        let ⟨m, h⟩ := MeasRender_total F Doc.nl c i (by constructor)
        by_cases h_c : c ≤ F.W 
        case pos => 
          exists MeasureSet.set [m] (by simp)
          constructor <;> assumption
        case neg => 
          replace h_c := Nat.gt_of_not_le h_c
          exists MeasureSet.tainted m
          constructor <;> simp [*]
      case neg => 
        replace h_i := Nat.gt_of_not_le h_i
        let ⟨m, h⟩ := MeasRender_total F Doc.nl c i (by constructor)
        exists MeasureSet.tainted m
        constructor <;> simp [*]
    | Doc.nest n d => 
      let ⟨ms, h⟩ := Resolve_total F d c (i + n)
      exists ms.lift (Meas.adjust_nest n) 
      constructor
      assumption
    | Doc.align d => 
      let ⟨ms, h⟩ := Resolve_total F d c c
      by_cases h_i : i ≤ F.W 
      case pos => 
        exists ms.lift (Meas.adjust_align i) 
        constructor <;> assumption
      case neg => 
        replace h_i := Nat.gt_of_not_le h_i
        exists ms.taint.lift (Meas.adjust_align i) 
        constructor <;> assumption
    | Doc.choice d₁ d₂ => 
      let ⟨ms₁, h₁⟩ := Resolve_total F d₁ c i
      let ⟨ms₂, h₂⟩ := Resolve_total F d₂ c i 
      exists MeasureSet.union F ms₁ ms₂
      constructor <;> assumption
    | Doc.concat d₁ d₂ => 
      let ⟨ms₁, h₁⟩ := Resolve_total F d₁ c i
      cases ms₁ 
      case tainted m₁ => 
        let ⟨ms₂, h₂⟩ := Resolve_total F d₂ m₁.lw i
        have : ∃ m₂, ms₂.taint = MeasureSet.tainted m₂ := by {
          cases ms₂
          all_goals { simp [MeasureSet.taint] }
        }
        let ⟨m₂, h₂'⟩ := this 
        exists MeasureSet.tainted (Meas.concat F m₁ m₂)
        constructor <;> assumption
      case set ms h_non_empty => 
        let ⟨msr, h'⟩ := ResolveConcat_total F ms d₂ i h_non_empty
        exists msr
        constructor <;> assumption
end
termination_by 
  ResolveConcatOne_total => (d.size, 1, 0)
  ResolveConcat_total => (d.size, 2, ms.length)
  Resolve_total => (d.size, 0, 0)