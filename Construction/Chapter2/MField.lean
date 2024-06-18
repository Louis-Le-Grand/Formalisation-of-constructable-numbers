import Construction.Chapter1.basic_construction

open Construction
noncomputable def MField (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): Subfield ℂ := {
  carrier := M_inf M
  zero_mem' := by exact M_M_inf M h₀
  one_mem' := by exact M_M_inf M h₁
  add_mem' := by apply add_M_Inf M h₀
  neg_mem' := by apply z_neg_M_inf M h₀
  mul_mem' := by apply mul_M_inf M h₀ h₁
  inv_mem' := by apply inv_M_inf M h₀ h₁
}

def quadratic_closed {F: Type*} [Field F] :=  ∀ x : F, ∃ y : F, y * y = x
