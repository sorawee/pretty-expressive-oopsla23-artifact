import Pretty.Supports.Basic

/-!
## Layout
-/

/--
Layout definition, which has at least one line (Section 3.1)
-/ 
inductive Layout where 
  | single (s : String) : Layout 
  | multi (first : String) (middle : List String) (last : String) : Layout

def Layout.max_with_offset (col_pos : ℕ) : Layout → ℕ 
| Layout.single s => col_pos + s.length
| Layout.multi first middle last =>
    max (col_pos + first.length) (max last.length ((middle.map String.length).foldl max 0))

def Layout.last (col_pos : ℕ) : Layout → ℕ 
| Layout.single s => col_pos + s.length
| Layout.multi _ _ last => last.length