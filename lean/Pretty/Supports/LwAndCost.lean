import Pretty.Defs.Basic
import Pretty.Supports.Basic
import Pretty.Supports.FactoryMath
import Pretty.Supports.Domination

/-!
Various lemmas about list of measures when 
they are decreasing in last length and increasing in cost.
-/

lemma lw_decreasing_head (h : lw_decreasing (x :: y :: xs)) :
    x.lw > y.lw := by
  exact h 0 (by simp) (by simp)

lemma lw_decreasing_rest (h : lw_decreasing (x :: xs)) :
    lw_decreasing xs := by
  intro i _ _ 
  exact h (i + 1) (by { simp_arith; linarith }) 
    (by { simp_arith; linarith })

lemma lw_decreasing_empty : @lw_decreasing α [] := by 
  intro _ _ _ 
  contradiction

lemma lw_decreasing_one : lw_decreasing [x] := by 
  intro _ _ _ 
  contradiction

lemma lw_decreasing_cons {α : Type} (x y : @Meas α) (xs : List Meas)
    (h_lw : x.lw > y.lw)
    (h : lw_decreasing (y :: xs)) : 
    lw_decreasing (x :: y :: xs) := by
  intro i _ _ 
  cases i 
  case zero => simp [h_lw]
  case succ i _ _ => 
    exact h i (by {
      simp_arith at *
      assumption
    }) (by {
      simp_arith at *
      assumption
    })

lemma lw_decreasing_strong (h : lw_decreasing ms) : 
  ∀ (i j : ℕ) (h_i : i < ms.length) (h_j : j < ms.length),
    i < j →
    (ms.get ⟨i, by assumption⟩).lw > (ms.get ⟨j, by assumption⟩).lw := by
  intro i j hi hj h_lt
  induction ms generalizing i j
  case nil => 
    simp at hi 
  case cons hd tl ih => 
    specialize ih (lw_decreasing_rest h)
    cases i 
    case zero => 
      cases j
      case zero => simp at h_lt
      case succ j => 
        cases tl 
        case nil => simp at hj
        case cons hd2 tl => 
          cases j 
          case zero => 
            simp [lw_decreasing_head h]
          case succ j => 
            have := lw_decreasing_head h
            simp at hj
            specialize ih 0 (j + 1) (by simp) (by {
              simp
              linarith
            }) (by simp)
            simp at ih
            dwi { apply lt_trans }
    case succ i => 
      cases j 
      case zero => simp at h_lt 
      case succ j => 
        simp at hi hj
        specialize ih i j (by linarith) (by linarith) (by linarith)
        simp [ih]

lemma cost_increasing_head (h : cost_increasing F (x :: y :: xs)) :
    F.lt x.cost y.cost := by
  exact h 0 (by simp) (by simp)

lemma cost_increasing_rest (h : cost_increasing F (x :: xs)) :
    cost_increasing F xs := by
  intro i _ _ 
  exact h (i + 1) (by { simp_arith; linarith }) 
    (by { simp_arith; linarith })

lemma cost_increasing_empty : cost_increasing F [] := by 
  intro _ _ _ 
  contradiction

lemma cost_increasing_one : cost_increasing F [x] := by 
  intro _ _ _ 
  contradiction

lemma cost_increasing_cons (x y : Meas) (xs : List Meas)
    (h_cost : F.lt x.cost y.cost)
    (h : cost_increasing F (y :: xs)) : 
    cost_increasing F (x :: y :: xs) := by
  intro i _ _ 
  cases i 
  case zero => simp [h_cost]
  case succ i _ _ => 
    exact h i (by {
      simp_arith at *
      assumption
    }) (by {
      simp_arith at *
      assumption
    })

lemma cost_increasing_strong (h : cost_increasing F ms) : 
  ∀ (i j : ℕ) (h_i : i < ms.length) (h_j : j < ms.length),
    i < j →
    F.lt (ms.get ⟨i, by assumption⟩).cost (ms.get ⟨j, by assumption⟩).cost := by
  intro i j hi hj h_lt
  induction ms generalizing i j
  case nil => 
    simp at hi 
  case cons hd tl ih => 
    specialize ih (cost_increasing_rest h)
    cases i 
    case zero => 
      cases j
      case zero => simp at h_lt
      case succ j => 
        cases tl 
        case nil => simp at hj
        case cons hd2 tl => 
          cases j 
          case zero => 
            simp [cost_increasing_head h]
          case succ j => 
            have := cost_increasing_head h
            simp at hj
            specialize ih 0 (j + 1) (by simp) (by {
              simp
              linarith
            }) (by simp)
            simp at ih
            dwi { apply F.lt_trans }
    case succ i => 
      cases j 
      case zero => simp at h_lt 
      case succ j => 
        simp at hi hj
        specialize ih i j (by linarith) (by linarith) (by linarith)
        simp [ih]

lemma cost_increasing_non_strict_head (h : cost_increasing_non_strict F (x :: y :: xs)) :
    F.le x.cost y.cost := by
  exact h 0 (by simp) (by simp)

lemma cost_increasing_non_strict_rest (h : cost_increasing_non_strict F (x :: xs)) :
    cost_increasing_non_strict F xs := by
  intro i _ _ 
  exact h (i + 1) (by { simp_arith; linarith }) 
    (by { simp_arith; linarith })

lemma cost_increasing_non_strict_empty : cost_increasing_non_strict F [] := by 
  intro _ _ _ 
  contradiction

lemma cost_increasing_non_strict_one : cost_increasing_non_strict F [x] := by 
  intro _ _ _ 
  contradiction

lemma cost_increasing_non_strict_cons (x y : Meas) (xs : List Meas)
    (h_cost : F.le x.cost y.cost)
    (h : cost_increasing_non_strict F (y :: xs)) : 
    cost_increasing_non_strict F (x :: y :: xs) := by
  intro i _ _ 
  cases i 
  case zero => simp [h_cost]
  case succ i _ _ => 
    exact h i (by {
      simp_arith at *
      assumption
    }) (by {
      simp_arith at *
      assumption
    })

lemma lw_decreasing_concat (F : Factory α) (m : Meas) (h : lw_decreasing ms) : lw_decreasing (ms.map (fun m' => Meas.concat F m m')) := by 
  induction ms 
  case nil => apply lw_decreasing_empty
  case cons hd tl ih => 
    specialize ih (lw_decreasing_rest h)
    cases tl 
    case nil => simp [lw_decreasing_one]
    case cons => 
      apply lw_decreasing_cons
      case h_lw => 
        replace h := lw_decreasing_head h 
        simp [h]
      case h => assumption 

lemma cost_increasing_non_strict_concat (m : Meas) (h : cost_increasing F ms) : cost_increasing_non_strict F (ms.map (fun m' => Meas.concat F m m')) := by 
  induction ms 
  case nil => apply cost_increasing_non_strict_empty
  case cons hd tl ih => 
    specialize ih (cost_increasing_rest h)
    cases tl 
    case nil => simp [cost_increasing_non_strict_one]
    case cons => 
      apply cost_increasing_non_strict_cons
      case h_cost => 
        replace h := cost_increasing_head h 
        simp [h]
        apply F.concat_monotonic 
        . apply F.le_refl 
        . apply Factory.le_of_lt
          assumption
      case h => assumption 

lemma lw_decreasing_bound (h : lw_decreasing ms) (i : ℕ) (hi : ms.length - 1 - i < ms.length) (h_bound : i < ms.length) : (ms.get ⟨ms.length - 1 - i, hi⟩).lw ≥ i := by 
  induction i
  case zero => simp
  case succ i ih => 
    simp
    cases ms 
    case nil => simp at hi 
    case cons hd tl =>
      simp at h_bound
      replace h_bound := Nat.lt_of_succ_lt_succ h_bound
      specialize ih (by simp_arith) (by {
        simp_arith
        exact Nat.le_of_lt h_bound
      })
      simp_arith at ih
      
      have := lw_decreasing_strong h _ ((hd :: tl).length - 1 - i) hi (by simp_arith) (by {
        simp
        generalize h_gen : tl.length = n
        simp [h_gen] at h_bound 
        clear * - h_bound 
        cases n
        case zero => simp at h_bound
        case succ => 
          simp 
          simp_arith at h_bound 
          dwi { apply Nat.sub_lt_sub_right }
      })
      simp at this
      have : i < ((hd :: tl).get ⟨(hd :: tl).length - 1 - Nat.succ i, hi⟩).lw := by {
        simp
        linarith
      }
      linarith