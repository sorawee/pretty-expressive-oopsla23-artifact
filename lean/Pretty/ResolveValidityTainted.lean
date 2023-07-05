import Pretty.ResolveValidity

mutual 
  theorem ResolveConcat_tainted_valid 
      (h_right : ResolveConcat F ms d₂ i (MeasureSet.tainted m)) 
      (h_widen₁ : Widen d₁ L₁) (h_widen₂ : Widen d₂ L₂)
      (h_left : Resolve F d₁ c i (MeasureSet.set orig_ms h_non_empty))
      (h_transfer : ∀ x, x ∈ ms → x ∈ orig_ms) :
      ∃ d_choiceless,
        d_choiceless ∈ List.join (List.map (fun d₁ => List.map (fun d₂ => Doc.concat d₁ d₂) L₂) L₁) ∧ MeasRender F  d_choiceless c i m := by 
    generalize h_ml : MeasureSet.tainted _ = ml at h_right
    cases h_right 
    case one h_current =>
      cases h_current 
      case set => contradiction
      case tainted h_current => 
        simp at h_ml h_transfer
        subst h_ml
        let ⟨d_left, _, h₁⟩ := Resolve_valid h_left h_widen₁ h_transfer
        let ⟨d_right, _, h₂⟩ := Resolve_tainted_valid h_current h_widen₂
        exists Doc.concat d_left d_right
        simp [*]
        dwi { constructor }
    case cons msr _ msr' h_rest h_current => 
      cases msr 
      case tainted => 
        cases h_current
        case set => contradiction
        case tainted m _ _ h_current => 
          specialize h_transfer m (by simp)
          simp [MeasureSet.union] at h_ml
          subst h_ml
          let ⟨d_left, _, h₁⟩ := Resolve_valid h_left h_widen₁ h_transfer
          let ⟨d_right, _, h₂⟩ := Resolve_tainted_valid h_current h_widen₂
          exists Doc.concat d_left d_right
          simp [*]
          dwi { constructor }
      case set => 
        cases msr' <;> simp [MeasureSet.union] at h_ml 

  theorem Resolve_tainted_valid (h_print : Resolve F d c i (MeasureSet.tainted m))
      (h_widen : Widen d D) : ∃ d_choiceless, d_choiceless ∈ D ∧ 
      MeasRender F d_choiceless c i m := by 
    match d with
    | Doc.text s => 
      cases h_print 
      exists Doc.text s
      constructor 
      case left => 
        cases h_widen 
        simp
      case right => assumption
    | Doc.nl => 
      cases h_print 
      exists Doc.nl 
      constructor 
      case left => 
        cases h_widen 
        simp
      case right => assumption
    | Doc.nest n d' => 
      generalize h_gen : MeasureSet.tainted _ = ml at h_print 
      cases h_print 
      case nest ms' h' => 
        cases ms' 
        case set => simp [MeasureSet.lift] at h_gen
        case tainted => 
          simp [MeasureSet.lift] at h_gen
          subst h_gen
          cases h_widen
          rename_i h_widen
          let ⟨d', h_in, h_render⟩ := Resolve_tainted_valid h' h_widen
          exists Doc.nest n d'
          simp [*]
          have := MeasRender_doc h_render (Widen_choiceless h_widen h_in)
          subst this 
          constructor
          simpa [Meas.adjust_nest]
    | Doc.align d' => 
      generalize h_gen : MeasureSet.tainted _ = ml at h_print 
      cases h_print 
      case align ms' h' _ => 
        cases ms' 
        case set => simp [MeasureSet.lift] at h_gen
        case tainted => 
          simp [MeasureSet.lift] at h_gen
          subst h_gen 
          cases h_widen
          rename_i h_widen
          let ⟨d', h_in, h_render⟩ := Resolve_tainted_valid h' h_widen
          exists Doc.align d' 
          simp [*]
          have := MeasRender_doc h_render (Widen_choiceless h_widen h_in)
          subst this 
          constructor
          simpa [Meas.adjust_align]
      case align_taint ms' _ _ => 
        cases h_widen
        rename_i h_widen
        cases ms' <;> simp [MeasureSet.lift, MeasureSet.taint] at h_gen <;> subst h_gen
        case tainted h' => 
          let ⟨d', h_in, h_render⟩ := Resolve_tainted_valid h' h_widen
          exists Doc.align d' 
          simp [*]
          have := MeasRender_doc h_render (Widen_choiceless h_widen h_in)
          subst this 
          constructor
          simpa [Meas.adjust_align]
        case set ms_res h_non_empty h' => 
          cases ms_res 
          case nil => contradiction 
          case cons hd tl => 
            have h_mem : hd ∈ hd :: tl := by simp
            let ⟨d', h_in, h_render⟩ := Resolve_valid h' h_widen h_mem
            exists Doc.align d' 
            simp [*]
            have := MeasRender_doc h_render (Widen_choiceless h_widen h_in)
            subst this 
            constructor
            simpa [Meas.adjust_align]
          
    | Doc.choice d₁ d₂ => 
      generalize h_gen : MeasureSet.tainted _ = ml at h_print 
      cases h_widen
      case choice h_widen₁ h_widen₂ =>
      cases h_print 
      case choice ms₁ ms₂ h₁ h₂ => 
        cases ms₁ 
        case tainted => 
          dwi { cases ms₂ } 
          case tainted => 
            simp [MeasureSet.union] at h_gen 
            subst h_gen
            let ⟨d', h_in, h_render⟩ := Resolve_tainted_valid h₁ h_widen₁
            exists d' 
            simp [h_in, h_render]
        case set ms' _ => 
          cases ms₂ <;> simp [MeasureSet.union] at h_gen
    | Doc.concat d₁ d₂ => 
      cases h_widen
      rename_i h_widen₁ h_widen₂
      cases h_print
      case concat_taint ms _ h_taint h_right h_left => 
        cases ms <;> simp [MeasureSet.taint] at h_taint <;> subst h_taint
        case tainted => 
          let ⟨d_left, _, h_left⟩ := Resolve_tainted_valid h_left h_widen₁
          let ⟨d_right, _, h_right⟩ := Resolve_tainted_valid h_right h_widen₂
          exists Doc.concat d_left d_right
          simp [*]
          dwi { constructor }
        case set ms_res h_non_empty => 
          cases ms_res 
          case nil => contradiction
          case cons hd tl => 
            have h_mem : hd ∈ hd :: tl := by simp
            let ⟨d_left, _, _⟩ := Resolve_tainted_valid h_left h_widen₁
            let ⟨d_right, _, _⟩ := Resolve_valid h_right h_widen₂ h_mem
            exists Doc.concat d_left d_right
            simp [*]
            dwi { constructor }
      case concat_set h_left h_print => 
        dwi { apply ResolveConcat_tainted_valid }

end
termination_by 
  ResolveConcat_tainted_valid => (d₁.size + d₂.size + 1, 0, ms.length)
  Resolve_tainted_valid => (d.size, 1, 0)