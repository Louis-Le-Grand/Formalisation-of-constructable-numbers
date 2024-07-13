import Construction.Chapter1.def

open Construction

/-
# Zero and One in MFinf
  Now we can fill in `zero_mem'` and `one_mem'` if we assume that `0, 1 ∈ M`.
-/
noncomputable def MField (M : Set ℂ): Subfield ℂ where
  carrier := M_inf M
  zero_mem' := sorry
  one_mem' := sorry
  mul_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry
  inv_mem' := sorry
