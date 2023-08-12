import Pretty.Supports.Basic

/-!
## Layout
-/

/--
Layout definition, which has at least one line (Section 3.1)
-/ 
inductive Layout where 
  | single (s : String) : Layout 
  | multi (first : String) 
          (middle : List (ℕ × String)) 
          (last : (ℕ × String)) : Layout

def Layout.max_with_offset (col_pos : ℕ) : Layout → ℕ 
| Layout.single s => col_pos + s.length
| Layout.multi first middle ⟨i_last, last⟩ =>
    max (col_pos + first.length) (max (i_last + last.length) ((middle.map (fun ⟨i_line, line⟩ => i_line + String.length line)).foldl max 0))

def Layout.last (col_pos : ℕ) : Layout → ℕ 
| Layout.single s => col_pos + s.length
| Layout.multi _ _ ⟨i_last, last⟩ => i_last + last.length