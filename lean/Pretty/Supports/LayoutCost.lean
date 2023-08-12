import Pretty.Defs.Basic 

lemma find_cost_extract : find_cost' F xs acc = F.concat acc (find_cost' F xs (F.text 0 0)) := by {
  induction xs generalizing acc
  case nil => simp [find_cost', Factory.text_id_right]
  case cons hd tl ih => 
    simp [find_cost']
    rw [ih, Factory.concat_assoc]
    conv => 
      right
      rw [ih]
    congr 2
    simp [Factory.text_id_left]
}

lemma find_cost_split : find_cost' F (xs ++ ys) acc = F.concat acc (F.concat (find_cost' F xs (F.text 0 0)) (find_cost' F ys (F.text 0 0))) := by {
  rw [find_cost_extract]
  congr 1
  induction xs generalizing ys
  case e_a.nil =>
    simp [find_cost', Factory.text_id_left]
  case e_a.cons hd_c tl ih => 
    let ⟨i_hd, hd⟩ := hd_c
    simp [find_cost']
    rw [find_cost_extract, ih]
    conv => 
      right 
      rw [find_cost_extract]
    simp [Factory.text_id_left, Factory.concat_assoc]
}