import Construction.Chapter1.set_Minf

open Construction

/-
# Zero and One in MFinf
  Now we can fill in `zero_mem'` and `one_mem'` if we assume that `0, 1 ∈ M`.
-/
noncomputable def MField (M : Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M): Subfield ℂ where
  carrier := M_inf M
  zero_mem' := M_M_inf M h₀
  one_mem' := M_M_inf M h₁
  mul_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry
  inv_mem' := sorry
