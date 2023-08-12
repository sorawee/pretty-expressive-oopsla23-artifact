import Pretty.Supports.Basic
import Pretty.Defs.Layout

/--
Cost factory interface definition (Figure 8)
-/
structure Factory (α : Type) where
  le : α → α → Bool
  concat : α → α → α 
  text : ℕ → ℕ → α 
  nl : ℕ → α
  W : ℕ

  text_monotonic : c ≤ c' → le (text c l) (text c' l)
  nl_monotonic : i ≤ i' → le (nl i) (nl i')
  concat_monotonic :  le cost₁ cost₂ → 
                      le cost₃ cost₄ → 
                      le (concat cost₁ cost₃) (concat cost₂ cost₄)

  le_trans : le c₁ c₂ → le c₂ c₃ → le c₁ c₃
  le_antisymm : le c₁ c₂ → le c₂ c₁ → c₁ = c₂
  le_total (c₁ c₂ : α) : le c₁ c₂ ∨ le c₂ c₁

  -- Not necessary for the correctness of the printer
  text_concat : concat (text c l₁) (text (c + l₁) l₂) = text c (l₁ + l₂)
  text_id_left : concat (text c 0) cost = cost 
  text_id_right : concat cost (text c 0) = cost 
  concat_assoc : concat (concat cost₁ cost₂) cost₃ = concat cost₁ (concat cost₂ cost₃)
