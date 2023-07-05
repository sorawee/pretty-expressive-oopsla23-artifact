import Pretty.Supports.Pareto

/--
The traditional definition of Pareto frontier based on non-domination
-/
def pareto_nondom (F : Factory α) (ms : List (@Meas α)) : Prop := 
  ∀ (i j : ℕ) (h_i : i < ms.length) (h_j : j < ms.length), 
    i ≠ j → 
    (¬ dominates F (ms.get ⟨i, by assumption⟩) (ms.get ⟨j, by assumption⟩) ∧  
       ¬ dominates F (ms.get ⟨j, by assumption⟩) (ms.get ⟨i, by assumption⟩))

/--
Our formalized definition of Pareto frontier is equivalent to the one in the paper based on non-domination.
-/
theorem pareto_nondom_iff_pareto : 
    pareto F ms ↔ (pareto_nondom F ms ∧ lw_decreasing ms) := by 
  apply Iff.intro
  case mp => 
    intro h
    apply And.intro 
    case left => 
      simp [pareto_nondom]
      intro i j hi hj h_neq 
      simp only [pareto] at h
      replace h_lw := lw_decreasing_strong h.left 
      replace h_cost := cost_increasing_strong h.right
      simp [dominates] 
      have h_tri := Nat.lt_trichotomy i j 
      cases h_tri 
      case inl h_tri => 
        specialize h_cost i j hi hj h_tri
        simp [h_lw i j hi hj h_tri]
        right 
        rw [← F.not_le_iff_lt] at h_cost
        simp at h_cost
        assumption
      case inr h_tri => 
        cases h_tri
        case inl h_tri => 
          simp [h_neq] at h_tri
        case inr h_tri => 
          specialize h_cost j i hj hi h_tri
          simp [h_lw j i hj hi h_tri]
          right
          rw [← F.not_le_iff_lt] at h_cost
          simp at h_cost
          assumption
    case right => simp [h.left]
  case mpr => 
    rintro ⟨h_pareto, h_lw⟩
    simp [pareto, h_lw, cost_increasing]
    intro i hi hj 
    specialize h_lw i hi hj 
    specialize h_pareto i (i + 1) hi hj (by simp)
    simp [dominates] at h_pareto
    replace h_pareto := h_pareto.right 
    simp at h_lw
    replace h_lw := Nat.le_of_lt h_lw
    specialize h_pareto h_lw 
    rw [← F.not_le_iff_lt]
    simp
    assumption