import Pretty.Claims.MeasRender

/--
Measure computation at higher column position or indentation level 
is worse
-/
lemma MeasRender_dom_monotonic {F : Factory α}
    (h : MeasRender F d c i m₁) (h' : MeasRender F d c' i' m₂)
    (h_c : c ≤ c') (h_i : i ≤ i') : dominates F m₁ m₂ := by {
  induction d generalizing c c' i i' m₁ m₂
  case text => 
    cases h
    cases h'
    simp only [
      dominates, add_le_add_iff_right, Bool.decide_and, Bool.decide_coe,
      Bool.and_eq_true, decide_eq_true_eq
    ]
    constructor
    case left => linarith 
    case right => dwi { apply F.text_monotonic }
  case nl =>
    cases h
    cases h'
    simp only [
      dominates, Bool.decide_and, Bool.decide_coe, Bool.and_eq_true, 
      decide_eq_true_eq
    ]
    dwi { constructor }
    case right => dwi { apply Factory.nl_monotonic }
      
  case nest ih | align ih =>
    cases h
    rename_i h
    cases h' 
    rename_i h'
    specialize ih h h' h_c (by simpa)
    assumption
  case concat ih₁ ih₂ => 
    cases h 
    case concat h₂ h₁ h_eq => 
    cases h' 
    case concat h₂' h₁' h_eq' => 
    specialize ih₁ h₁ h₁' h_c (by assumption)
    simp only [
      dominates, Bool.decide_and, Bool.decide_coe,
      Bool.and_eq_true, decide_eq_true_eq
    ] at ih₁
    specialize ih₂ h₂ h₂' (by simp [ih₁]) (by assumption)
    simp [dominates] at ih₂ ⊢ 
    constructor
    case left => simp [*]
    case right => 
      simp [*]
      apply Factory.concat_monotonic
      . simp [ih₁.right]
      . simp [ih₂]
  case choice => cases h
}

/--
Measure computation on a choiceless document preserves 
the doc component
-/
lemma MeasRender_doc (h_render : MeasRender F d c i m) (h : Choiceless d) : m.doc = d := by {
  let ⟨⟨s, ss⟩, h⟩ := @Render_total d c i h
  cases ss 
  case nil => 
    let ⟨cost, ⟨y, h_render'⟩⟩ := MeasRender_single_line_correct F h
    cases MeasRender_deterministic h_render h_render'
    simp
  case cons hd tl => 
    let ⟨cost, ⟨y, h_render'⟩⟩ := MeasRender_multi_line_correct F h (by simp)
    cases MeasRender_deterministic h_render h_render'
    simp
}

/--
If measure computation at higher column position or indentation level 
does not exceed the computation width limit, then the current measure computation 
also does not exceed the computation width limit
-/
lemma MeasRender_dom_is_good {F : Factory α}
    (h : MeasRender F d c i m₁) (h' : MeasRender F d c' i' m₂)
    (h_c : c ≤ c') (h_i : i ≤ i') (h_x : m₂.x ≤ F.W) (h_y : m₂.y ≤ F.W) : 
    m₁.x ≤ F.W ∧ m₁.y ≤ F.W := by {
  induction d generalizing c c' i i' m₁ m₂
  case text => 
    cases h
    cases h'
    simp only [
      dominates, add_le_add_iff_right, Bool.decide_and, Bool.decide_coe,
      Bool.and_eq_true, decide_eq_true_eq
    ]
    constructor
    case left => linarith 
    case right => 
      simp at h_y 
      dwi { apply le_trans } 

  case nl =>
    cases h
    cases h'
    simp only [
      dominates, Bool.decide_and, Bool.decide_coe, Bool.and_eq_true, 
      decide_eq_true_eq
    ]
    constructor 
    case left => 
      simp at h_x h_y ⊢   
      constructor 
      case left => 
        apply le_trans 
        . assumption 
        . simp [h_x]
      case right => 
        apply le_trans 
        . assumption
        . simp [h_y]
    case right => 
      simp at h_y 
      dwi { apply le_trans } 
  case nest ih =>
    cases h
    rename_i h
    cases h' 
    rename_i h'
    simp at ih h_x h_y ⊢
    exact ih h h' h_c (by simpa) h_x h_y
  case align ih =>
    cases h
    rename_i h
    cases h' 
    rename_i h'
    simp at ih h_x h_y ⊢
    have := ih h h' h_c (by simpa) h_x (by {
      simp [h_y] 
    })
    simp at this 
    constructor 
    case left => simp [*]
    case right => 
      constructor 
      case left => 
        apply le_trans 
        . assumption
        . simp [h_y]
      case right => simp [*]  
  case concat ih₁ ih₂ => 
    cases h 
    case concat h₂ h₁ h_eq => 
    subst h_eq
    cases h' 
    case concat h₂' h₁' h_eq' => 
    subst h_eq'
    simp at h_x h_y ⊢
    have := MeasRender_dom_monotonic h₁ h₁' h_c h_i
    specialize ih₁ h₁ h₁' h_c (by assumption) (by simp [h_x]) (by simp [h_y])
    simp only [
      dominates, Bool.decide_and, Bool.decide_coe,
      Bool.and_eq_true, decide_eq_true_eq
    ] at ih₁
    specialize ih₂ h₂ h₂' (by {
      simp [dominates] at this
      simp [this]
    }) (by assumption)
    simp [dominates] at ih₂ ⊢ 
    constructor
    case left => simp [*]
    case right => 
      simp [*]
  case choice => cases h
}