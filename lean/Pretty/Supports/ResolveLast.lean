import Pretty.Supports.ResolvePareto

/-!
This set of lemmas states that a measure set from resolving will consist of 
measures whose last line length is bound by $W$
-/

mutual
  lemma ResolveConcatOne_last
      (h : ResolveConcatOne F d m_left i (MeasureSet.set ms h_not_empty))
      (h_in : m ∈ ms) : 
      m.last ≤ F.W := by
    cases h 
    case set h => 
      have := dedup_member h_in 
      simp at this 
      let ⟨m', h_mem, h'⟩ := this
      subst h' 
      simp [Meas.concat]
      exact Resolve_last h h_mem 

  lemma ResolveConcat_last 
      {h_not_empty : ms ≠ []}
      (h : ResolveConcat F ms_in d i (MeasureSet.set ms h_not_empty))
      (h_in : m ∈ ms) : 
      m.last ≤ F.W := by 
    generalize h_meas : MeasureSet.set ms h_not_empty = ml at h
    cases h 
    case one h_current => 
      apply ResolveConcatOne_last 
      case h => 
        subst h_meas
        apply h_current
      case h_in => assumption
    case cons ms' _ ms'' h_rest h_current => 
      cases ms' 
      case tainted => 
        simp [MeasureSet.union] at h_meas 
        subst h_meas 
        dwi { apply ResolveConcatOne_last }
      case set => 
        cases ms'' 
        case tainted => 
          simp [MeasureSet.union] at h_meas 
          subst h_meas 
          apply ResolveConcat_last h_rest h_in
        case set => 
          simp [MeasureSet.union] at h_meas 
          subst h_meas 
          have := merge_pareto_subset h_in (ResolveConcatOne_pareto h_current) (ResolveConcat_pareto h_rest)
          cases this 
          case inl h_in' => 
            dwi { apply ResolveConcatOne_last }
          case inr h_in' =>
            apply ResolveConcat_last h_rest h_in'
      
  lemma Resolve_last
      {h_not_empty : ms ≠ []}
      (h : Resolve F d c i (MeasureSet.set ms h_not_empty)) 
      (h_in : m ∈ ms) : 
      m.last ≤ F.W := by 
    cases d
    case text => 
      cases h 
      case text_set h_c h_i h_meas => 
        simp at h_in 
        subst h_in
        cases h_meas 
        simp
        assumption
    case nl => 
      cases h 
      case line_set h_c h_i h_meas => 
        simp at h_in 
        subst h_in
        cases h_meas 
        simp
        assumption
    case nest n _ ih => 
      generalize h_meas : MeasureSet.set ms h_not_empty = ml at h
      cases h
      case nest ms' h  => 
        cases ms' 
        case tainted => simp [MeasureSet.lift] at h_meas
        case set => 
          simp [MeasureSet.lift] at h_meas
          subst h_meas
          simp at h_in
          let ⟨m', h_left, h_right⟩ := h_in
          have ih := Resolve_last h h_left
          simp [Meas.adjust_nest] at h_right
          cases m 
          simp at h_right ⊢ 
          simp [← h_right.left]
          assumption
    case align ih => 
      generalize h_meas : MeasureSet.set ms h_not_empty = ml at h
      cases h
      case align ms' h _ => 
        cases ms' 
        case tainted => simp [MeasureSet.lift] at h_meas
        case set => 
          simp [MeasureSet.lift] at h_meas
          subst h_meas
          simp at h_in
          let ⟨m', h_left, h_right⟩ := h_in
          have ih := Resolve_last h h_left
          simp [Meas.adjust_align] at h_right
          cases m 
          simp at h_right ⊢ 
          simp [← h_right.left]
          assumption
      case align_taint ms h _ => 
        cases ms 
        case set | tainted => simp [MeasureSet.lift, MeasureSet.taint] at h_meas
    case reset ih => 
      generalize h_meas : MeasureSet.set ms h_not_empty = ml at h
      cases h
      case reset ms' h _ => 
        cases ms' 
        case tainted => simp [MeasureSet.lift] at h_meas
        case set => 
          simp [MeasureSet.lift] at h_meas
          subst h_meas
          simp at h_in
          let ⟨m', h_left, h_right⟩ := h_in
          have ih := Resolve_last h h_left
          simp [Meas.adjust_reset] at h_right
          cases m 
          simp at h_right ⊢ 
          simp [← h_right.left]
          assumption
      case reset_taint ms h _ => 
        cases ms 
        case set | tainted => simp [MeasureSet.lift, MeasureSet.taint] at h_meas
    case choice ih₁ ih₂ => 
      generalize h_meas : MeasureSet.set ms h_not_empty = ml at h
      cases h
      case choice ms'' ms' h_left h_right => 
        cases ms' 
        case tainted => 
          simp [MeasureSet.union] at h_meas 
          subst h_meas 
          exact Resolve_last h_left h_in
        case set h_not_empty' => 
          cases ms'' 
          case tainted => 
            simp [MeasureSet.union] at h_meas 
            subst h_meas 
            exact Resolve_last h_right h_in
          case set => 
            simp [MeasureSet.union] at h_meas 
            subst h_meas 
            have := merge_pareto_subset h_in (Resolve_pareto h_left) (Resolve_pareto h_right)
            cases this
            case inl h_in' => exact Resolve_last h_left h_in' 
            case inr h_in' => exact Resolve_last h_right h_in' 
    case concat ih₁ _ => 
      cases h 
      case concat_set h_left h_right =>
        dwi { apply ResolveConcat_last }
end
termination_by 
  ResolveConcatOne_last => (d.size, 1, 0)
  ResolveConcat_last => (d.size, 2, ms_in.length)
  Resolve_last => (d.size, 0, 0)