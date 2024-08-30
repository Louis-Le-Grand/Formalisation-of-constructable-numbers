import Construction.Chapter1.basic_construction
import Mathlib.FieldTheory.Adjoin

section pre
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

def conj_set (M : Set ℂ) : Set ℂ := {starRingEnd ℂ z | z ∈ M}

noncomputable def conj_field (K : Subfield ℂ) : Subfield ℂ where
  carrier := conj_set K
  mul_mem' := sorry
  one_mem' := sorry
  add_mem' := sorry
  zero_mem' := sorry
  neg_mem' := sorry
  inv_mem' := sorry

class ConjClosed (M : Set ℂ) : Prop where
  equal: M = conj_set M

end pre


open IntermediateField Construction Complex Polynomial

variable (L : Subfield ℂ) [ConjClosed L]

lemma icc_L (z : ℂ) (h : z ∈ icc L): ∃ ω ∈ L,∃ x : ℂ, x * x = ω ∧ z ∈ L⟮x⟯ := by sorry
