import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.ClearExcept
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Lemmas

/-!
## Basic lemmas about built-in types
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
