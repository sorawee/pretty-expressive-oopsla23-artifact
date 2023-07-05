import Pretty.ResolveLemma
import Pretty.MergeLemma
import Pretty.DocSizeLemma

mutual
  lemma ResolveConcatOne_pareto 
      (h_print : ResolveConcatOne F d m i (MeasureSet.set msr h_non_empty)) : 
      pareto F msr := by 
    cases h_print
    case set h => exact pareto_concat _ (Resolve_pareto h)

  lemma ResolveConcat_pareto 
      (h_print : ResolveConcat F ms d i (MeasureSet.set msr h_non_empty)) : 
      pareto F msr := by
    
    generalize h_gen : MeasureSet.set _ _ = ms at h_print
    cases h_print 
    case one h_print => 
      subst h_gen
      exact ResolveConcatOne_pareto h_print 
    case cons msr_left _ msr_right h_rest h_print => 
      cases msr_left 
      case tainted => 
        cases msr_right 
        case tainted => simp [MeasureSet.union] at h_gen
        case set => 
          simp [MeasureSet.union] at h_gen  
          subst h_gen 
          exact ResolveConcatOne_pareto h_print 
      case set => 
        cases msr_right 
        case tainted => 
          simp [MeasureSet.union] at h_gen  
          subst h_gen
          exact ResolveConcat_pareto h_rest
        case set => 
          simp [MeasureSet.union] at h_gen  
          subst h_gen 
          apply merge_preserves_pareto 
          case h_pareto₁ => exact ResolveConcatOne_pareto h_print 
          case h_pareto₂ => exact ResolveConcat_pareto h_rest

  theorem Resolve_pareto (h_print : Resolve F d c i (MeasureSet.set ms h_non_empty)) : 
      pareto F ms := by 
    generalize h_gen : MeasureSet.set _ _ = ms at h_print
    match d with
    | Doc.text _ => 
      subst h_gen
      cases h_print 
      case text_set => apply pareto_one
    | Doc.nl => 
      subst h_gen
      cases h_print
      case line_set => apply pareto_one
    | Doc.nest n d' =>
      dwi { cases h_print } 
      case nest ms' h' => 
        dwi { cases ms' } 
        case set => 
          simp [MeasureSet.lift] at h_gen
          subst h_gen
          apply pareto_map_lift_nest
          exact Resolve_pareto h'
    | Doc.align d' =>
      cases h_print 
      case align ms' h' _ => 
        dwi { cases ms' } 
        case set => 
          simp [MeasureSet.lift] at h_gen
          subst h_gen
          apply pareto_map_lift_align
          exact Resolve_pareto h'
      case align_taint ms' _ _ => dwi { cases ms' }
    | Doc.choice d₁ d₂ => 
      dwi { cases h_print } 
      case choice ms ms' h_left h_right => 
        cases ms 
        case tainted => 
          cases ms'
          case tainted => simp [MeasureSet.union] at h_gen 
          case set => 
            simp [MeasureSet.union] at h_gen 
            subst h_gen 
            exact Resolve_pareto h_right
        case set => 
          cases ms'
          case tainted => 
            simp [MeasureSet.union] at h_gen 
            subst h_gen 
            exact Resolve_pareto h_left
          case set => 
            simp [MeasureSet.union] at h_gen 
            have := Resolve_pareto h_left 
            have := Resolve_pareto h_right 
            subst h_gen
            apply merge_preserves_pareto <;> assumption
    | Doc.concat d₁ d₂ => 
      dwi { cases h_print } 
      case concat_set h_left h_print => 
        dwi { cases ms } 
        case set => 
          cases h_gen
          exact ResolveConcat_pareto h_print 
end
termination_by 
  ResolveConcatOne_pareto => (d.size, 1, 0)
  ResolveConcat_pareto => (d.size, 2, ms.length)
  Resolve_pareto => (d.size, 0, 0)