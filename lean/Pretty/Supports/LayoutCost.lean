import Pretty.Defs.Basic 

lemma compute_cost_extract : compute_cost F xs acc = F.concat acc (compute_cost F xs (F.text 0 0)) := by {
  induction xs generalizing acc
  case nil => simp [compute_cost, Factory.text_id_right]
  case cons hd tl ih => 
    simp [compute_cost]
    rw [ih, Factory.concat_assoc]
    conv => 
      right
      rw [ih]
    congr 2
    simp [Factory.text_id_left]
}

lemma compute_cost_split : compute_cost F (xs ++ ys) acc = F.concat acc (F.concat (compute_cost F xs (F.text 0 0)) (compute_cost F ys (F.text 0 0))) := by {
  rw [compute_cost_extract]
  congr 1
  induction xs generalizing ys
  case e_a.nil =>
    simp [compute_cost, Factory.text_id_left]
  case e_a.cons hd_c tl ih => 
    let ⟨i_hd, hd⟩ := hd_c
    simp [compute_cost]
    rw [compute_cost_extract, ih]
    conv => 
      right 
      rw [compute_cost_extract]
    simp [Factory.text_id_left, Factory.concat_assoc]
}