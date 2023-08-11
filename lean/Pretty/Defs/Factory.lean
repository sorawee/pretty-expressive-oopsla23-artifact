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

/-!
### Cost for a bigtext
-/

def Factory.bigtext (F : Factory α) : Layout → ℕ → α
| Layout.single s, c => F.text c s.length
| Layout.multi first [] last, c => 
  F.concat (F.text c first.length) (F.concat (F.nl 0) (F.text 0 last.length))
| Layout.multi first (line :: lines) last, c => 
  F.concat (F.text c first.length) (F.concat (F.nl 0) (F.bigtext (Layout.multi line lines last) 0))
