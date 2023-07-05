import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.ClearExcept

/-!
Basic lemmas about built-in types
-/

lemma List.fold_max_max_eq_max_fold_max : 
    ∀ {a b : ℕ}, List.foldl max (max a b) xs = max a (List.foldl max b xs) := by {
  induction xs 
  case nil => simp
  case cons ih => simp [ih, max_assoc]
}

lemma List.get_index_eq {xs : List α} {i j : ℕ} (hi : i < xs.length) (h : i = j) : 
    ∃ (hj : j < xs.length), xs.get ⟨i, hi⟩ = xs.get ⟨j, hj⟩ := by 
  simp [h] at hi
  exists hi 
  simp [h]

lemma List.get_zero_eq_head {xs : List α} (hn : xs ≠ []) :
    xs.get ⟨0, by { cases xs; contradiction; simp }⟩ = xs.head hn := by 
  cases xs; contradiction; simp

lemma Nat.not_lt_of_lt {a b : ℕ} (h : a < b): ¬ b < a := by linarith

lemma Nat.mul_lt_mul₀ {a b c d : Nat} (h1 : a < c) (h2 : b < d) : a * b < c * d := 
  match b with 
  | 0 => 
    match c with 
    | 0 => match h1 with .
    | c+1 => by simp [h2]
  | b+1 => Nat.mul_lt_mul h1 (Nat.le_of_lt h2) (by simp)

lemma Nat.sub_lt_sub_right {a b c : Nat} (h0 : a < b) (h1 : c ≤ a) : 
    a - c < b - c := by {
  induction c 
  case zero => 
    simpa 
  case succ ih => 
    simp [Nat.sub_succ]
    apply Nat.pred_lt_pred
    . simp 
      linarith
    . apply ih 
      linarith
}

lemma Nat.sub_sub_eq {a b c : Nat} (h : a ≤ b) : c + a - b = c - (b - a) := by {
  let ⟨k, h'⟩ := Nat.le.dest h 
  rw [←h']
  simp [Nat.sub_add_eq]
}