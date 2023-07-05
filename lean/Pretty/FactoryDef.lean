import Pretty.Basic

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