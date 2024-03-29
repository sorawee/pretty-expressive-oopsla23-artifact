import Pretty.Defs.Layout
import Pretty.Defs.Factory
import Pretty.Supports.FactoryMath

/-!
## Basic definitions

### Document
-/

/--
Document definition (syntax of $\Sigma_e$, Figure 4).
One deviation is that we don't include the `flatten` construct, as explained in Section 6.2 / 6.7.
-/ 
inductive Doc where 
  | text (s : String) : Doc
  | nl : Doc
  | concat (d₁ d₂ : Doc) : Doc
  | nest (n : Nat) (d : Doc) : Doc
  | align (d : Doc) : Doc
  | reset (d : Doc) : Doc
  | choice (d₁ d₂ : Doc) : Doc

def Doc.size : Doc → ℕ
  | Doc.text _ => 1 
  | Doc.nl => 1
  | Doc.concat d₁ d₂ => Doc.size d₁ + Doc.size d₂ + 1 
  | Doc.nest _ d => Doc.size d + 1
  | Doc.align d => Doc.size d + 1
  | Doc.reset d => Doc.size d + 1
  | Doc.choice d₁ d₂ => Doc.size d₁ + Doc.size d₂ + 1

/--
Choiceless document definition (Section 3.1),
defined as a predicate on `Doc`.
-/ 
inductive Choiceless : Doc → Prop where 
  | text (s : String) : Choiceless (Doc.text s)
  | nl : Choiceless Doc.nl
  | concat (d₁ d₂ : Doc) (h₁ : Choiceless d₁) (h₂ : Choiceless d₂) : 
      Choiceless (Doc.concat d₁ d₂)
  | nest (n : Nat) (d : Doc) (h : Choiceless d) : Choiceless (Doc.nest n d)
  | align (d : Doc) (h : Choiceless d) : Choiceless (Doc.align d)
  | reset (d : Doc) (h : Choiceless d) : Choiceless (Doc.reset d)

/-!
### Rendering and widening
-/

/--
Rendering relation definition ($⇓_\mathcal{R}$, Figure 8).
One deviation is that the flattening mode is not included, as explained in Section 6.2 / 6.7.
-/ 
inductive Render : Doc → ℕ → ℕ → Layout → Prop where
  | text : Render (Doc.text s) c i (Layout.single s)
  | nl : Render Doc.nl c i (Layout.multi "" [] ⟨i, ""⟩)
  | concat_single_single
      (h₁ : Render d₁ c i (Layout.single s₁)) 
      (h₂ : Render d₂ (c + s₁.length) i (Layout.single s₂)) : 
      Render (Doc.concat d₁ d₂) c i (Layout.single (s₁ ++ s₂))
  | concat_single_multi
      (h₁ : Render d₁ c i (Layout.single s₁)) 
      (h₂ : Render d₂ (c + s₁.length) i (Layout.multi first₂ middle₂ last₂)) : 
      Render (Doc.concat d₁ d₂) c i (Layout.multi (s₁ ++ first₂) middle₂ last₂)
  | concat_multi_single
      (h₁ : Render d₁ c i (Layout.multi first₁ middle₁ ⟨i_last₁, last₁⟩)) 
      (h₂ : Render d₂ (i_last₁ + last₁.length) i (Layout.single s₂)) : 
      Render (Doc.concat d₁ d₂) c i (Layout.multi first₁ middle₁ ⟨i_last₁, last₁ ++ s₂⟩)
  | concat_multi_multi
      (h₁ : Render d₁ c i (Layout.multi first₁ middle₁ ⟨i_last₁, last₁⟩))
      (h₂ : Render d₂ (i_last₁ + last₁.length) i (Layout.multi first₂ middle₂ last₂)) : 
      Render (Doc.concat d₁ d₂) c i (Layout.multi first₁ (middle₁ ++ [⟨i_last₁, last₁ ++ first₂⟩] ++ middle₂) last₂)
  | nest (h : Render d c (i + n) L) : Render (Doc.nest n d) c i L
  | align (h : Render d c c L) : Render (Doc.align d) c i L
  | reset (h : Render d c 0 L) : Render (Doc.reset d) c i L

/--
Widening relation definition ($⇓_\mathcal{W}$, Figure 8)
-/ 
inductive Widen : Doc → List Doc → Prop where
  | text (s : String) : Widen (Doc.text s) [Doc.text s]
  | nl : Widen Doc.nl [Doc.nl]
  | concat (h₁ : Widen d₁ L₁) (h₂ : Widen d₂ L₂) : 
      Widen (Doc.concat d₁ d₂) (L₁.map (fun d₁ => L₂.map (fun d₂ => Doc.concat d₁ d₂))).join 
  | nest (h : Widen d L) : Widen (Doc.nest n d) (L.map (fun d => Doc.nest n d))
  | align (h : Widen d L) : Widen (Doc.align d) (L.map (fun d => Doc.align d))
  | reset (h : Widen d L) : Widen (Doc.reset d) (L.map (fun d => Doc.reset d))
  | choice (h₁ : Widen d₁ L₁) (h₂ : Widen d₂ L₂) : 
      Widen (Doc.choice d₁ d₂) (L₁ ++ L₂) 

section Cost 
 
variable {α : Type}
variable (F : Factory α)

def compute_cost : List (ℕ × String) → α → α
  | [], acc => acc
  | ⟨i, s⟩ :: l, acc => 
    compute_cost l (F.concat acc (F.concat (F.nl i) (F.text i s.length)))

def Layout.find_cost (c : ℕ) : Layout → α
  | Layout.single s => F.text c s.length
  | Layout.multi first middle last => 
    compute_cost F (middle ++ [last]) (F.text c first.length)

end Cost

section Meas

/-!
### Measure
-/

variable {α : Type}
variable (F : Factory α)

/--
Measure definition (Figure 12)
-/ 
structure Meas where
  last : ℕ
  cost : α  
  doc : Doc 
  x : ℕ
  y : ℕ  

/-!
### Various measure operations (Figure 12)
-/ 

/--
- adjustAlign;
-/ 
def Meas.adjust_align (i : ℕ): @Meas α → @Meas α
| ⟨last, cost, doc, x, y⟩ => ⟨last, cost, Doc.align doc, x, max i y⟩

/--
- adjustReset;
-/ 
def Meas.adjust_reset (i : ℕ): @Meas α → @Meas α
| ⟨last, cost, doc, x, y⟩ => ⟨last, cost, Doc.reset doc, x, max i y⟩

/--
- adjustNest;
-/ 
def Meas.adjust_nest (n : ℕ): @Meas α → @Meas α
| ⟨last, cost, doc, x, y⟩ => ⟨last, cost, Doc.nest n doc, x, y⟩

/--
- concatenation (∘); and
-/ 
@[reducible]
def Meas.concat : @Meas α → @Meas α → @Meas α
  | ⟨_, cost₁, d₁, x₁, y₁⟩, ⟨last₂, cost₂, d₂, x₂, y₂⟩ => 
    ⟨last₂, F.concat cost₁ cost₂, Doc.concat d₁ d₂, max x₁ x₂, max y₁ y₂⟩ 

/--
- domination (≼)
-/ 
def dominates (m₁ m₂ : @Meas α) : Bool := 
  m₁.last ≤ m₂.last ∧ F.le m₁.cost m₂.cost

/-!
### Measure computation/rendering
-/

/--
Measure computation/rendering definition (Figure 13)
-/ 
inductive MeasRender : Doc → ℕ → ℕ → Meas → Prop where
  | text (s : String) : 
      MeasRender (Doc.text s) c i 
        (Meas.mk (c + s.length) (F.text c s.length) (Doc.text s) (c + s.length) i)
  | nl : MeasRender Doc.nl c i (Meas.mk i (F.nl i) Doc.nl (max c i) i)
  | concat
      (h₁ : MeasRender d₁ c i m₁) 
      (h₂ : MeasRender d₂ m₁.last i m₂)
      (h : m = Meas.concat F m₁ m₂) : 
      MeasRender (Doc.concat d₁ d₂) c i m
  | nest (h : MeasRender d c (i + n) (Meas.mk last cost d x y)) :
      MeasRender (Doc.nest n d) c i (Meas.mk last cost (Doc.nest n d) x y)
  | align (h : MeasRender d c c (Meas.mk last cost d x y)) :
      MeasRender (Doc.align d) c i (Meas.mk last cost (Doc.align d) x (max i y))
  | reset (h : MeasRender d c 0 (Meas.mk last cost d x y)) :
      MeasRender (Doc.reset d) c i (Meas.mk last cost (Doc.reset d) x (max i y))
end Meas 

section Pareto

variable (F : Factory α)

/-!
### Pareto frontier
-/

/--
A list of measures is strictly increasing in cost
-/ 
def cost_increasing (ms : List (@Meas α)) : Prop := 
  ∀ i (hi : i < ms.length) (hj : i + 1 < ms.length), 
    F.lt (ms.get ⟨i, hi⟩).cost (ms.get ⟨i + 1, hj⟩).cost

/--
A list of measures is (non-strictly) increasing in cost
-/
def cost_increasing_non_strict (ms : List (@Meas α)) : Prop := 
  ∀ i (hi : i < ms.length) (hj : i + 1 < ms.length), 
    F.le (ms.get ⟨i, hi⟩).cost (ms.get ⟨i + 1, hj⟩).cost

/--
A list of measures is strictly decreasing in length of last line
-/
def last_decreasing (ms : List (@Meas α)) : Prop := 
  ∀ i (hi : i < ms.length) (hj : i + 1 < ms.length), 
    (ms.get ⟨i, hi⟩).last > (ms.get ⟨i + 1, hj⟩).last

/--
A predicate that a list of measures form a Pareto frontier (Section 5.4)
This definition is not the same as the definition described in the paper, 
which is based on non-domination. However, they are equivalent, 
proven at `pareto_nondom_iff_pareto` in `Pretty.Claims.Pareto`.
-/
def pareto (ms : List (@Meas α)) : Prop := 
  last_decreasing ms ∧ cost_increasing F ms

end Pareto

section ListMeasure

variable (F : Factory α)

/-!
### Various list of measures operations (Figure 14)
-/

/--
- dedup;
-/
def dedup : List (@Meas α) → List (@Meas α)
  | [] => []
  | [m] => [m]
  | m₁ :: m₂ :: ms => 
    if F.le m₂.cost m₁.cost then dedup (m₂ :: ms)
    else m₁ :: dedup (m₂ :: ms)

/--
- merge (⊎);
-/
def merge : List (@Meas α) × List (@Meas α) → List (@Meas α)
  | ⟨[], ms⟩  => ms
  | ⟨ms, []⟩ => ms
  | ⟨m₁ :: ms₁, m₂ :: ms₂⟩ => 
    if dominates F m₁ m₂ then merge ⟨m₁ :: ms₁, ms₂⟩ 
    else if dominates F m₂ m₁ then merge ⟨ms₁, m₂ :: ms₂⟩ 
    else if m₁.last > m₂.last then m₁ :: merge ⟨ms₁, m₂ :: ms₂⟩ 
    else m₂ :: merge ⟨m₁ :: ms₁, ms₂⟩ 

/-!
### Measure set
-/

/--
Measure set definition (Figure 14).
Unlike the definition in the paper, we carry the proof that `ms` is non-empty 
instead of relying on the implicit non-empty assumption everywhere.
-/
inductive MeasureSet : Type where 
  | tainted (m : @Meas α) : MeasureSet
  | set (ms : List (@Meas α)) (h : ms ≠ []) : MeasureSet

end ListMeasure
