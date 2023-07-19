import Pretty.Defs.Layout

lemma Layout.last_monotonic (h : c ≤ c') (l : Layout) : l.last c ≤ l.last c' := by 
  cases l <;> simp [Layout.last, h]

lemma Layout.max_with_offset_monotonic (l : Layout) (h : c ≤ c') : l.max_with_offset c ≤ l.max_with_offset c' := by 
  cases l
  case single => simp [Layout.max_with_offset, h]
  case multi first middle last => 
    simp only [Layout.max_with_offset]
    generalize max (String.length last) (List.foldl max 0 (List.map String.length middle)) = q₁ 
    generalize first.length = q₂
    by_cases h₁ : q₁ ≤ c + q₂
    case pos => simp [h₁, h]
    case neg => 
      simp at h₁
      by_cases h₂ : q₁ ≤ c' + q₂
      case pos => simp [h, h₁, h₂]
      case neg => 
        simp at h₂
        simp [h, h₁, h₂]
        right
        apply Nat.le_of_lt
        assumption



      
      