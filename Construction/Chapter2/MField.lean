import Construction.Chapter1.basic_construction
import Mathlib.FieldTheory.IsAlgClosed.Basic

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

noncomputable instance MField_field (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): Field (MField M h₀ h₁) := by
  exact SubfieldClass.toField (Subfield ℂ) (MField M h₀ h₁)

--? TODO: Add to blueprint
lemma MField_mem (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): ∀ x : ℂ, x ∈ MField M h₀ h₁ ↔ x ∈ M_inf M := by
  intro x
  exact @Subfield.mem_carrier ℂ _ (MField M h₀ h₁) x

lemma MField_i (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): Complex.I ∈ MField M h₀ h₁ := by
  exact imath_M_inf M h₀ h₁

--? TODO: Add to blueprint
lemma MField_i_mul (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): ∀ x : ℝ, ↑x ∈ MField M h₀ h₁ ↔ Complex.I * x ∈ MField M h₀ h₁ := by
  intro x
  constructor
  exact @Subfield.mul_mem ℂ _ (MField M h₀ h₁) (Complex.I) x (MField_i M h₀ h₁)
  exact i_z_imp_z_in_M_inf M h₀ h₁ x

lemma MField_re_im (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): ∀ x : ℂ, x ∈ MField M h₀ h₁ ↔ ↑x.re ∈ MField M h₀ h₁ ∧ ↑x.im ∈ MField M h₀ h₁  := by
  exact z_iff_re_im_M_inf M h₀ h₁

lemma MField_re_im' (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): ∀ x : ℂ, x ∈ MField M h₀ h₁ ↔ ↑x.re ∈ MField M h₀ h₁ ∧ Complex.I * x.im ∈ MField M h₀ h₁ := by
  intro x
  rw[←MField_i_mul M h₀ h₁]
  exact z_iff_re_im_M_inf M h₀ h₁ x

--TODO: Add iff for polar coordinates
