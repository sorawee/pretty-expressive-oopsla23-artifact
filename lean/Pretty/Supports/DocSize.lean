import Pretty.Defs.Basic

/-!
## Various lemmas about size of `Doc`

These will be helpful for termination proofs. 
They will be used implicitly, as we mark them with `@[simp]`.
-/

@[simp]
lemma Doc.size_choice₁ : Doc.size d₁ < Doc.size (Doc.choice d₁ d₂) := by simp_arith [Doc.size]

@[simp]
lemma Doc.size_choice₂ : Doc.size d₂ < Doc.size (Doc.choice d₁ d₂) := by simp_arith [Doc.size]

@[simp]
lemma Doc.size_align : Doc.size d' < Doc.size (Doc.align d') := by simp_arith [Doc.size]

@[simp]
lemma Doc.size_reset : Doc.size d' < Doc.size (Doc.reset d') := by simp_arith [Doc.size]

@[simp]
lemma Doc.size_nest : Doc.size d' < Doc.size (Doc.nest n d') := by simp_arith [Doc.size]

@[simp]
lemma Doc.size_concat₁ : d₁.size < (Doc.concat d₁ d₂).size := by simp_arith [Doc.size]

@[simp]
lemma Doc.size_concat₂ : d₂.size < (Doc.concat d₁ d₂).size := by simp_arith [Doc.size]