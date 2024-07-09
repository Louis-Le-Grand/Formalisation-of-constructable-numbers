import Construction.Chapter1.basic_construction

open Construction

noncomputable def MField (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): Subfield ℂ where
  carrier := M_inf M
  zero_mem' := by exact M_M_inf M h₀
  one_mem' := by exact M_M_inf M h₁
  add_mem' := sorry
  neg_mem' := sorry
  mul_mem' := sorry
  inv_mem' := sorry
