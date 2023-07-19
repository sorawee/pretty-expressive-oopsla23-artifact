import Pretty.Defs.Resolve
import Pretty.Supports.MeasRender
import Pretty.Supports.ResolvePareto
import Pretty.Supports.ResolveOptimal
import Pretty.Claims.Widen

/-!
## Optimality theorems
-/

mutual
  /--
  The optimality theorem (Theorem 5.7)
  -/
  theorem Resolve_optimal 
      (h_print : Resolve F d c i ml)
      (h_widen : Widen d D) (h_mem : d_choiceless ∈ D) 
      (h_render : MeasRender F d_choiceless c i m)
      (h_y : m.y ≤ F.W) (h_x : m.x ≤ F.W) :
      ∃ ms h, ml = MeasureSet.set ms h ∧ ∃ m_better, m_better ∈ ms ∧ dominates F m_better m := by
    match d with
    | Doc.text s => 
      apply Resolve_optimal_text <;> assumption
    | Doc.bigtext s => 
      apply Resolve_optimal_bigtext <;> assumption
    | Doc.nl => 
      apply Resolve_optimal_nl <;> assumption
    | Doc.nest n d => 
      cases h_widen 
      rename_i h_widen
      simp at h_mem
      let ⟨_, ⟨h_left, h_right⟩⟩ := h_mem
      subst h_right
      simp
      cases h_print 
      case nest ms' h' => 
        simp at *
        cases ms' 
        case tainted => 
          cases h_render
          rename_i h_render
          simp 
          have := Resolve_optimal h' h_widen h_left (by assumption)
          simp at this h_x h_y
          cases this h_y h_x
        case set printed_ms h_render' => 
          simp [MeasureSet.lift, Meas.adjust_nest]
          cases h_render
          rename_i h_render
          have h_now := Resolve_optimal h' h_widen h_left h_render h_y h_x
          simp [dominates] at h_now
          exists printed_ms.map (Meas.adjust_nest n)
          simp [Meas.adjust_nest, dominates]
          assumption
    | Doc.align d => 
      cases h_widen 
      rename_i h_widen
      simp at h_mem
      let ⟨_, ⟨h_left, h_right⟩⟩ := h_mem
      subst h_right
      simp
      cases h_print 
      case align ms' h' _ => 
        simp at *
        cases ms' 
        case tainted => 
          cases h_render
          rename_i h_render
          simp 
          have := Resolve_optimal h' h_widen h_left (by assumption)
          simp at this h_x h_y
          let ⟨_, h_y⟩ := h_y
          cases this h_y h_x
        case set printed_ms h_render' => 
          simp [MeasureSet.lift, Meas.adjust_nest]
          cases h_render
          rename_i h_render
          have h_now := Resolve_optimal h' h_widen h_left h_render
          simp [dominates] at h_now h_x h_y
          let ⟨_, h_y⟩ := h_y
          specialize h_now h_y h_x
          exists printed_ms.map (Meas.adjust_align i)
          simp [Meas.adjust_align, dominates]
          assumption
      case align_taint ms' h h_bad => 
        cases h_render
        rename_i h_render
        simp at h_y 
        clear * - h_y h_bad 
        linarith
    | Doc.choice d₁ d₂ => 
      cases h_widen 
      rename_i h_widen₁ h_widen₂
      simp at h_mem
      cases h_print
      case choice ms₁ ms₂ h_left h_right => 
        cases ms₁ 
        case tainted => 
          cases h_mem 
          case inl h_mem => 
            have := Resolve_optimal h_left h_widen₁ h_mem (by assumption)
            let ⟨_, _, _, _⟩ := this h_y h_x
            contradiction
          case inr h_mem => 
            have := Resolve_optimal h_right h_widen₂ h_mem (by assumption)
            let ⟨ms, _, h_left, h_right⟩ := this h_y h_x
            subst h_left
            exists ms, (by assumption)
        case set => 
          cases h_mem 
          case inl h_mem => 
            have := Resolve_optimal h_left h_widen₁ h_mem (by assumption)
            let ⟨ms_left, _, h_left', h_right'⟩ := this h_y h_x
            cases ms₂
            case tainted => 
              simp [MeasureSet.union]
              simp at h_left' 
              subst h_left'
              constructor <;> assumption
            case set => 
              let ⟨m_better, h_mem_b, _⟩ := h_right'
              simp [MeasureSet.union]
              constructor 
              case left => 
                apply merge_not_empty
                simp [*]
              case right => 
                cases h_left'
                let ⟨m_better, ⟨h_mem, h_dom⟩⟩ := merge_dom₁ (Resolve_pareto h_left) (Resolve_pareto h_right) h_mem_b
                exists m_better 
                simp [*]
                dwi { apply dominates_trans } 
          case inr h_mem => 
            have := Resolve_optimal h_right h_widen₂ h_mem (by assumption)
            let ⟨_, _, ⟨h_left', m_better, h_mem_b, _⟩⟩ := this h_y h_x 
            cases ms₂
            case tainted => simp at h_left' 
            case set => 
              simp [MeasureSet.union]
              constructor 
              case left => 
                apply merge_not_empty
                simp [*]
              case right => 
                cases h_left'
                let ⟨m_better, ⟨h_mem, h_dom⟩⟩ := merge_dom₂ (Resolve_pareto h_left) (Resolve_pareto h_right) h_mem_b
                exists m_better 
                simp [*]
                dwi { apply dominates_trans } 
    | Doc.concat d₁ d₂ => 
      cases h_widen 
      rename_i h_widen₁ h_widen₂
      simp at h_mem
      let ⟨d_left, h_left, d_right, h_right, h_concat⟩ := h_mem
      clear h_mem
      subst h_concat
      cases h_print
      case concat_taint h_taint h_right' h_left' => 
        cases h_render
        rename_i hh_right hh_left hh
        subst hh
        simp [Meas.concat] at h_y h_x
        let ⟨_, _, _, _⟩ := Resolve_optimal h_left' h_widen₁ h_left hh_left h_y.left h_x.left
        contradiction
      case concat_set ms h_non_empty h_left' h_right' => 
        cases h_render
        rename_i m₁ m₂ hh_right hh_left hh
        subst hh
        simp [Meas.concat] at h_x h_y
        let ⟨ms_left, h_mem_left, h_eq, m_better, h_mem', h_dom⟩ := Resolve_optimal h_left' h_widen₁ h_left hh_left h_y.left h_x.left
        cases h_eq
        apply ResolveConcat_optimal <;> assumption
    
  theorem ResolveConcat_optimal
      (h_print: ResolveConcat F ms d₂ i ml)
      (h_widen: Widen d₂ L₂)
      (h_choiceless: d_right ∈ L₂)
      (h_render: MeasRender F d_right m₁.last i m₂)
      (h_x: m₁.x ≤ F.W ∧ m₂.x ≤ F.W)
      (h_y: m₁.y ≤ F.W ∧ m₂.y ≤ F.W)
      (h_dom: dominates F m_better_left m₁)
      (h_mem: m_better_left ∈ ms) :
         ∃ ms h, ml = MeasureSet.set ms h ∧ ∃ m_better, m_better ∈ ms ∧ dominates F m_better (Meas.concat F m₁ m₂) := by 
  cases h_print 
  case one h_print => 
    simp at h_mem
    subst h_mem
    exact ResolveConcatOne_optimal h_widen h_choiceless h_print h_render h_x h_y h_dom 
  case cons msr' the_m msr h_rest h_print => 
    cases h_mem 
    case head => 
      have := ResolveConcatOne_optimal h_widen h_choiceless h_print h_render h_x h_y h_dom 
      let ⟨ms, _, h_eq, h_other⟩ := this
      subst h_eq 
      cases msr'
      case tainted => 
        exists ms, (by simp [*])
      case set => 
        have h_pareto := ResolveConcatOne_pareto h_print 
        have h_pareto' := ResolveConcat_pareto h_rest
        simp [MeasureSet.union]
        constructor 
        case left => 
          apply merge_not_empty 
          simp [*]
        case right => 
          let ⟨m, hh⟩ := h_other
          let ⟨mm, hhh⟩ := merge_dom₁ h_pareto h_pareto' hh.left
          exists mm 
          simp [hhh]
          apply dominates_trans 
          . apply hhh.right 
          . apply hh.right
    case tail h_mem =>
      let ⟨ms, h_non_empty, h₁, h₂⟩ := ResolveConcat_optimal h_rest h_widen h_choiceless h_render h_x h_y h_dom h_mem
      subst h₁ 
      cases msr 
      case tainted => 
        cases h_print 
        simp [MeasureSet.union, h_non_empty, h₂]
      case set => 
        have h_pareto := ResolveConcatOne_pareto h_print
        simp [MeasureSet.union] 
        constructor
        case left => 
          apply merge_not_empty
          simp [*]
        case right => 
          let ⟨m_better, h_better⟩ := h₂
          have h_pareto' := ResolveConcat_pareto h_rest
          have h_pareto := ResolveConcatOne_pareto h_print
          have := merge_dom₂ h_pareto h_pareto' (by {
            exact h_better.left
          })
          let ⟨mm, hh⟩ := this
          exists mm
          simp [hh]
          apply dominates_trans 
          . exact hh.right
          . exact h_better.right

  theorem ResolveConcatOne_optimal
      (h_widen: Widen d₂ L₂)
      (h_choiceless: d_right ∈ L₂)
      (h_print: ResolveConcatOne F d₂ m_better i ml)
      (h_render: MeasRender F d_right m₁.last i m₂)
      (h_x: m₁.x ≤ F.W ∧ m₂.x ≤ F.W)
      (h_y: m₁.y ≤ F.W ∧ m₂.y ≤ F.W)
      (h_dom: dominates F m_better m₁) :
         ∃ ms h, ml = MeasureSet.set ms h ∧ ∃ m_better, m_better ∈ ms ∧ dominates F m_better (Meas.concat F m₁ m₂) := by 
    have h_is_choiceless := Widen_choiceless h_widen h_choiceless
    let ⟨m_result_better, h_render_better⟩ := MeasRender_total F d_right m_better.last i h_is_choiceless 
    have h_dom_better := MeasRender_dom_monotonic h_render_better h_render (by {
      simp [dominates] at h_dom
      simp [h_dom]
    }) (by simp)
    have h_dom_good := MeasRender_dom_is_good h_render_better h_render (by {
      simp [dominates] at h_dom
      simp [h_dom]
    }) (by simp) (by simp [h_x]) (by simp [h_y])
    cases h_print
    case tainted h_print => 
      have := Resolve_optimal h_print h_widen h_choiceless (by assumption) h_dom_good.right h_dom_good.left 
      let ⟨_, _, _, _⟩ := this
      contradiction
    case set ms _ h_print => 
      have := Resolve_optimal h_print h_widen h_choiceless (by assumption) h_dom_good.right h_dom_good.left 
      let ⟨_, h, h_left, m_better_right, h_better_right⟩ := this
      cases h_left
      exists dedup F (ms.map (fun m' => Meas.concat F m_better m')), (by {
        apply dedup_not_empty
        simp [h]
      })
      simp
      have h_pareto := Resolve_pareto h_print
      have h_cost := cost_increasing_non_strict_concat m_better h_pareto.right
      have h_last := last_decreasing_concat F m_better h_pareto.left
      let ⟨m_ult, h_mem_ult, h_dom_ult⟩ := dedup_dom 
        (List.mem_map_of_mem (fun m' => Meas.concat F m_better m')
        h_better_right.left) h_last h_cost
      exists m_ult 
      simp [h_mem_ult]
      clear * - h_dom_ult h_dom h_dom_better h_better_right
      simp [dominates] at h_dom_ult h_dom h_dom_better h_better_right ⊢  
      constructor 
      case left => 
        have aa := h_dom_ult.left
        have bb := h_better_right.right.left 
        have cc := h_dom_better.left
        clear * - aa bb cc
        linarith 
      case right => 
        have aa := h_dom_ult.right
        have bb := h_better_right.right.right
        have cc := h_dom_better.right
        have dd := h_dom.right
        apply Factory.le_trans 
        . assumption
        . apply Factory.concat_monotonic 
          . apply dd
          . apply Factory.le_trans 
            . assumption 
            . assumption
end
termination_by 
  Resolve_optimal => (d.size, 0, 0)
  ResolveConcat_optimal => (d₂.size, 2, ms.length)
  ResolveConcatOne_optimal => (d₂.size, 1, 0)