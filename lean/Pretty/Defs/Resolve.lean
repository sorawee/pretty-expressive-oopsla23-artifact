import Pretty.Defs.Basic
import Pretty.Defs.MeasureSetOp
import Pretty.Supports.Dedup

section Resolve 

variable (F : Factory α)

mutual 
  inductive Resolve : Doc → ℕ → ℕ → @MeasureSet α → Prop where 
    | line_taint (h_bad : c > F.W ∨ i > F.W) (h : MeasRender F Doc.nl c i m) : 
        Resolve Doc.nl c i (MeasureSet.tainted m)
    | line_set (h_c : c ≤ F.W) (h_i : i ≤ F.W) (h : MeasRender F Doc.nl c i m) : 
        Resolve Doc.nl c i (MeasureSet.set [m] (by simp))
    | text_taint (h_bad : c + s.length > F.W ∨ i > F.W) (h : MeasRender F (Doc.text s) c i m) : 
        Resolve (Doc.text s) c i (MeasureSet.tainted m)
    | text_set (h_c : c + s.length ≤ F.W) (h_i : i ≤ F.W) (h : MeasRender F (Doc.text s) c i m) : 
        Resolve (Doc.text s) c i (MeasureSet.set [m] (by simp))
    | bigtext_taint {l : Layout} (h_bad : l.max_with_offset c > F.W ∨ i > F.W) (h : MeasRender F (Doc.bigtext l) c i m) : 
        Resolve (Doc.bigtext l) c i (MeasureSet.tainted m)
    | bigtext_set {l : Layout} (h_c : l.max_with_offset c ≤ F.W) (h_i : i ≤ F.W) (h : MeasRender F (Doc.bigtext l) c i m) : 
        Resolve (Doc.bigtext l) c i (MeasureSet.set [m] (by simp))
    | align_taint (h_bad : i > F.W) (h : Resolve d c c ms) : 
        Resolve (Doc.align d) c i (ms.taint.lift (Meas.adjust_align i))
    | align (h_ok : i ≤ F.W) (h : Resolve d c c ms) : 
        Resolve (Doc.align d) c i (ms.lift (Meas.adjust_align i))
    | nest (h : Resolve d c (i + n) ms) : Resolve (Doc.nest n d) c i (ms.lift (Meas.adjust_nest n))
    | choice (h_left : Resolve d c i ms) (h_right : Resolve d' c i ms') : 
        Resolve (Doc.choice d d') c i (MeasureSet.union F ms ms')
    | concat_taint (h_left : Resolve d c i (MeasureSet.tainted m)) (h_right : Resolve d' m.last i ms') (h_taint : ms'.taint = MeasureSet.tainted m') : (Resolve (Doc.concat d d') c i (MeasureSet.tainted (Meas.concat F m m')))
    | concat_set (h_left : Resolve d c i (MeasureSet.set ms h_non_empty)) 
        (h : ResolveConcat ms d' i msr) : 
        Resolve (Doc.concat d d') c i msr

  inductive ResolveConcat : List Meas → Doc → ℕ → MeasureSet → Prop where
    | one (h_current : ResolveConcatOne d m i msr) : ResolveConcat [m] d i msr
    | cons (h_rest : ResolveConcat ms d i msr) 
           (h_current : ResolveConcatOne d m i msr') :
           ResolveConcat (m :: ms) d i (MeasureSet.union F msr' msr)
  
  inductive ResolveConcatOne : Doc → Meas → ℕ → MeasureSet → Prop where
    | tainted (h : Resolve d m.last i (MeasureSet.tainted m')) : 
        ResolveConcatOne d m i (MeasureSet.tainted (Meas.concat F m m'))
    | set (h : Resolve d m.last i (MeasureSet.set ms h_non_empty)) : 
        ResolveConcatOne d m i (MeasureSet.set (dedup F (ms.map (fun m' => Meas.concat F m m'))) (by {
            apply dedup_not_empty 
            simp [h_non_empty]
        }))
end

end Resolve