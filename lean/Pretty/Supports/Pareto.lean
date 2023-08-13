import Pretty.Defs.Basic
import Pretty.Supports.Basic
import Pretty.Supports.FactoryMath
import Pretty.Supports.Domination
import Pretty.Supports.LastAndCost
import Pretty.Supports.Dedup

/-!
Various lemmas about `pareto`.
-/

lemma pareto_head (h : pareto F (m :: m' :: ms)) : 
    m.last > m'.last ∧ F.lt m.cost m'.cost := by 
  constructor 
  case left => exact last_decreasing_head h.left
  case right => exact cost_increasing_head h.right

lemma pareto_rest {ms : List Meas} {m : Meas} 
    (h : pareto F (m :: ms)) : pareto F ms := by 
  constructor
  case left => exact last_decreasing_rest h.left
  case right => exact cost_increasing_rest h.right

lemma pareto_drop (n : ℕ) (h : pareto F ms) : pareto F (ms.drop n) := by 
  induction ms generalizing n
  case nil => simpa
  case cons hd tl ih => 
    dwi { cases n } 
    case succ n => exact ih n (pareto_rest h)

lemma pareto_rest' (h : pareto F (m :: m' :: ms)) : pareto F (m :: ms) := by 
  simp [pareto, cost_increasing, last_decreasing] at *
  constructor
  case left => 
    intros i hi hj 
    cases ms 
    case nil => simp at hj 
    case cons hd _ _ => 
      cases i
      case zero => 
        have h₁ := h.left 0 (by simp) (by simp)
        have h₂ := h.left 1 (by simp) (by { simp [Nat.succ_lt_succ] })
        simp at h₁ h₂ ⊢ 
        linarith
      case succ i => 
        simp at hi hj 
        rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one] at hi hj
        simp at hi hj 
        have h' := h.left (i + 2) (by { simp; rw [Nat.succ_eq_add_one]; simpa }) (by { simp; rw [Nat.succ_eq_add_one]; simpa })
        simpa
  case right =>
    intros i hi hj 
    cases ms 
    case nil => simp at hj 
    case cons hd _ _ => 
      cases i
      case zero => 
        have h₁ := h.right 0 (by simp) (by simp_arith)
        have h₂ := h.right 1 (by simp) (by simp_arith)
        simp at h₁ h₂ ⊢ 
        apply Factory.lt_trans <;> assumption
      case succ i => 
        simp [Nat.succ_eq_add_one, Nat.succ_eq_add_one] at hi hj
        have h' := h.right (i + 2) (by { simp; rw [Nat.succ_eq_add_one]; simpa }) (by { simp; rw [Nat.succ_eq_add_one]; simpa })
        simpa 

lemma pareto_one (m : Meas) : pareto F [m] := by 
  simp [pareto, cost_increasing_one, last_decreasing_one]

lemma pareto_cons (ms : List Meas) (x y : Meas) 
    (h_last : x.last > y.last)
    (h_cost : F.lt x.cost y.cost)
    (h : pareto F (y :: ms)) : 
    pareto F (x :: y :: ms) := by
  simp only [pareto] at *
  constructor
  case left => 
    apply last_decreasing_cons 
    case h_last => simp [h_last]
    case h => simp [h]
  case right =>
    apply cost_increasing_cons 
    case h_cost => assumption
    case h => simp [h]

lemma pareto_concat (m : Meas) (h : pareto F ms) : 
    pareto F (dedup F (ms.map (fun m' => Meas.concat F m m'))) := by 
  simp only [pareto] at * 
  constructor
  case left => 
    apply dedup_last_decreasing
    apply last_decreasing_concat
    apply h.left
  case right => 
    apply dedup_cost_increasing
    apply cost_increasing_non_strict_concat
    apply h.right

lemma pareto_map_lift_align (n : ℕ) (h : pareto F ms) : 
    pareto F (ms.map (Meas.adjust_align n)) := by 
  induction ms
  case nil => simpa
  case cons tl ih => 
    cases tl
    case nil => apply pareto_one
    case cons => 
      dwi { apply pareto_cons } 
      case h => 
        apply ih
        apply pareto_rest 
        assumption
      case h_last | h_cost => 
        replace h := pareto_head h 
        simp [Meas.adjust_align, h]

lemma pareto_map_lift_reset (n : ℕ) (h : pareto F ms) : 
    pareto F (ms.map (Meas.adjust_reset n)) := by 
  induction ms
  case nil => simpa
  case cons tl ih => 
    cases tl
    case nil => apply pareto_one
    case cons => 
      dwi { apply pareto_cons } 
      case h => 
        apply ih
        apply pareto_rest 
        assumption
      case h_last | h_cost => 
        replace h := pareto_head h 
        simp [Meas.adjust_reset, h]

lemma pareto_map_lift_nest (n : ℕ) (h : pareto F ms) : 
    pareto F (ms.map (Meas.adjust_nest n)) := by 
  induction ms
  case nil => simpa
  case cons tl ih => 
    cases tl
    case nil => apply pareto_one
    case cons => 
      dwi { apply pareto_cons } 
      case h => 
        apply ih
        apply pareto_rest 
        assumption
      case h_last | h_cost => 
        replace h := pareto_head h 
        simp [Meas.adjust_nest, h]