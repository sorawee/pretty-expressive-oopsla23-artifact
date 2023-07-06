import Pretty.Supports.LastAndCost

/-! 
## Various lemmas related to the `dedup` operation
-/

lemma dedup_not_empty (h : ms ≠ []) : dedup F ms ≠ [] := by 
  induction ms 
  case nil => contradiction
  case cons hd tl ih => 
    cases tl 
    case nil => simp [dedup]
    case cons hd' tl' => 
      simp [dedup]
      split_ifs
      case inl => simp [ih]
      case inr => simp

lemma dedup_member (h : m ∈ dedup F ms) : m ∈ ms := by 
  induction ms 
  case nil => simp [dedup] at h
  case cons hd tl ih => 
    cases tl
    case nil => 
      simp [dedup] at h
      simp [h]
    case cons hd' tl' => 
      simp [dedup] at h 
      split_ifs at h 
      case inl => 
        specialize ih h 
        rw [List.mem_cons]
        right
        assumption
      case inr => 
        simp at h 
        cases h 
        case inl h => simp [h]
        case inr h => 
          specialize ih h 
          rw [List.mem_cons]
          right 
          assumption  

lemma dedup_last_first (h : dedup F (m :: ms) = m' :: ms')
    (h_last : last_decreasing (m :: ms)) : 
    m.last ≥ m'.last := by 
  induction ms generalizing m
  case nil => 
    simp [dedup] at h 
    simp [h]
  case cons hd tl ih => 
    simp [dedup] at h 
    split_ifs at h
    case inl h_if => 
      specialize ih h (last_decreasing_rest h_last)
      replace h_last := last_decreasing_head h_last
      clear * - h_last ih
      linarith
    case inr => 
      simp at h
      simp [h]
      
lemma dedup_last_decreasing (h : last_decreasing ms) : last_decreasing (dedup F ms) := by 
  induction ms 
  case nil => simpa [dedup]
  case cons x tl ih => 
    cases tl 
    case nil => simpa [dedup]
    case cons x' tl' => 
      simp [dedup]
      split_ifs
      case inl => 
        apply ih 
        apply last_decreasing_rest
        assumption
      case inr => 
        cases h_case : dedup F (x' :: tl')
        case nil => apply last_decreasing_one 
        case cons => 
          rw [h_case] at ih
          apply last_decreasing_cons 
          case h_last => 
            replace h_case := dedup_last_first h_case (last_decreasing_rest h)
            simp at h_case ⊢ 
            replace h := last_decreasing_head h
            simp at h
            clear * - h_case h
            linarith
          case h => 
            apply ih 
            apply last_decreasing_rest  
            assumption

lemma dedup_cost_first (h : dedup F (m :: ms) = m' :: ms')
    (h_last : cost_increasing_non_strict F (m :: ms)) : 
    m.cost = m'.cost := by 
  induction ms generalizing m
  case nil => 
    simp [dedup] at h 
    simp [h]
  case cons hd tl ih =>
    simp [dedup] at h 
    split_ifs at h
    case inl h_if => 
      specialize ih h (cost_increasing_non_strict_rest h_last)
      replace h_last := cost_increasing_non_strict_head h_last
      have := F.le_antisymm h_last h_if 
      rw [this, ih]
    case inr => 
      simp at h
      simp [h]
  
lemma dedup_cost_increasing (h : cost_increasing_non_strict F ms) : cost_increasing F (dedup F ms) := by 
  induction ms 
  case nil =>  
    intro i hi hj 
    simp [dedup] at hi 
  case cons x tl ih => 
    cases tl 
    case nil => 
      simp [dedup]
      apply cost_increasing_one
    case cons y tl => 
      simp [dedup]
      split_ifs 
      case inl => 
        apply ih 
        apply cost_increasing_non_strict_rest 
        assumption
      case inr h_if => 
        replace h := cost_increasing_non_strict_rest h
        specialize ih h
        rw [Factory.not_le_iff_lt] at h_if
        cases h_case : dedup F (y :: tl) 
        case nil => apply cost_increasing_one
        case cons => 
          replace h := dedup_cost_first h_case h
          apply cost_increasing_cons
          case h => 
            simp [h_case] at ih 
            assumption
          case h_cost => 
            rw [←h]
            apply h_if 

lemma dedup_cons (m' : Meas) (h : m ∈ dedup F ms) : m ∈ dedup F (m' :: ms) := by 
  cases ms 
  case nil => simp [dedup] at h
  case cons x tl => 
    simp [dedup]
    split_ifs
    case inl => assumption
    case inr => 
      apply List.Mem.tail 
      assumption

lemma dedup_dom (h : m ∈ ms) (h_last : last_decreasing ms) (h_cost : cost_increasing_non_strict F ms) : ∃ m_better, m_better ∈ dedup F ms ∧ dominates F m_better m := by {
  induction ms
  case nil => contradiction
  case cons x ms ih => 
    cases h 
    case head => 
      cases ms 
      case nil => simp [dedup, dominates_refl]
      case cons y ms => 
        simp [dedup]
        split_ifs 
        case inl => 
          cases h_case : dedup F (y :: ms) 
          case nil => 
            have : dedup F (y :: ms) ≠ [] := by {
              apply dedup_not_empty
              simp
            }
            contradiction
          case cons hd tl => 
            exists hd 
            simp 
            have h_last' := dedup_last_first h_case (last_decreasing_rest h_last)
            have h_cost' := dedup_cost_first h_case (cost_increasing_non_strict_rest h_cost)
            simp [dominates]
            constructor 
            case left => 
              have h_last'' := last_decreasing_head h_last 
              clear * - h_last' h_last''
              linarith
            case right => 
              rw [←h_cost']
              assumption
        case inr => simp [dominates_refl]
    case tail h => 
      let ⟨m_better, h, h_dom⟩ := ih h (last_decreasing_rest h_last) (cost_increasing_non_strict_rest h_cost)
      exists m_better
      replace h := dedup_cons x h
      simp [h, h_dom]     
}