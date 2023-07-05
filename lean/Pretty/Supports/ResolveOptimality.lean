import Pretty.Defs.Resolve
import Pretty.Claims.MeasRender
import Pretty.Supports.ResolvePareto

theorem Resolve_optimal_text
      (h_print : Resolve F (Doc.text s) c i ml)
      (h_widen : Widen (Doc.text s) D) (h_mem : d_choiceless ∈ D) 
      (h_render : MeasRender F d_choiceless c i m)
      (h_y : m.y ≤ F.W) (h_x : m.x ≤ F.W) :
      ∃ ms h, ml = MeasureSet.set ms h ∧ ∃ m_better, m_better ∈ ms ∧ dominates F m_better m := by
  cases h_widen 
  simp at h_mem 
  subst h_mem
  cases h_print 
  case text_set h' => 
    have := MeasRender_deterministic h_render h' 
    subst this 
    exists [m], (by simp)
    simp [dominates_refl]
  case text_taint h_bad h_render' => 
    cases h_render
    simp at h_y h_x 
    cases h_bad 
    case inl h_bad => linarith
    case inr h_bad => linarith

theorem Resolve_optimal_nl
      (h_print : Resolve F Doc.nl c i ml)
      (h_widen : Widen Doc.nl D) (h_mem : d_choiceless ∈ D) 
      (h_render : MeasRender F d_choiceless c i m)
      (h_y : m.y ≤ F.W) (h_x : m.x ≤ F.W) :
      ∃ ms h, ml = MeasureSet.set ms h ∧ ∃ m_better, m_better ∈ ms ∧ dominates F m_better m := by
  cases h_widen 
  simp at h_mem 
  subst h_mem
  cases h_print 
  case line_set h' => 
    have := MeasRender_deterministic h_render h' 
    subst this 
    exists [m], (by simp)
    simp [dominates_refl]
  case line_taint h_bad h_render' => 
    cases h_render
    simp at h_y h_x 
    cases h_bad 
    case inl h_bad => linarith
    case inr h_bad => linarith