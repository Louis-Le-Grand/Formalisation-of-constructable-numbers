import Construction.Chapter1.def

open Construction

/-
# Now we can fill in the carrier
-/
noncomputable def MField (M : Set ℂ): Subfield ℂ where
  carrier := M_inf M
  mul_mem' := sorry
  one_mem' := sorry
  add_mem' := sorry
  zero_mem' := sorry
  neg_mem' := sorry
  inv_mem' := sorry
