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
lemma icc_L' (z :ℂ) {c₁ c₂ : Construction.circle} (hc₁: c₁ ∈ C L) (hc₂: c₂ ∈ C L) (h_ne : c₁.points' ≠ c₂.points'): z ∈ c₁.points ∩ c₂.points ↔
  ∃ l :line, l ∈ Construction.L L ∧  z ∈ l.points ∩ c₁.points ∧ z ∈ l.points ∩ c₂.points := by
  refine ⟨?_,?_⟩ <;> intro h
  . by_cases hx: c₁.c.re = c₂.c.re
    . have: c₁.c.im ≠ c₂.c.im := by
        by_contra hy
        have h_eq: c₁.c = c₂.c := Complex.ext hx hy
        simp only [circle.points', h_eq, ne_eq, EuclideanGeometry.Sphere.mk.injEq, true_and] at h_ne
        simp only [circle.points, h_eq, Set.mem_inter_iff, mem_sphere_iff_norm, norm_eq_abs] at h
        obtain ⟨left, right⟩ := h
        simp_all only [not_true_eq_false]
      sorry
    . by_cases hy: c₁.c.im = c₂.c.im
      . sorry
      -- use z₁ z₂ from pdf
      sorry
  . obtain ⟨_, _ , h₁, h₂⟩ := h
    exact ⟨Set.mem_of_mem_inter_right h₁,Set.mem_of_mem_inter_right h₂⟩

example (a b c :ℝ): a = b ∧ a = c → b= c := by
  intro a_1
  obtain ⟨left, right⟩ := a_1
  subst right left
  simp_all only
