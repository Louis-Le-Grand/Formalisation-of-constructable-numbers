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

variable (L : Subfield ℂ) [ConjClosed L]

lemma ir_L (z : ℂ) (h : z ∈ L): ↑z.re ∈ L := by sorry


lemma im_L (z : ℂ) (h : z ∈ L): z.im * Complex.I ∈ L := by sorry


lemma distSq_L (z₁ z₂ : ℂ) (h₁ : z₁ ∈ L) (h₂ : z₂ ∈ L): ↑(Complex.normSq (z₁ - z₂)) ∈ L := by sorry

end pre


open IntermediateField Construction Complex Polynomial

variable (L : Subfield ℂ) [ConjClosed L]

lemma ir_im_iff_L (z : ℂ): z ∈ L ↔ ↑z.re ∈ L ∧ z.im * Complex.I ∈ L := by
  refine ⟨?_,?_⟩ <;> intro h
  . exact ⟨ir_L L z h, im_L L z h⟩
  . obtain ⟨h₁, h₂⟩ := h
    rw [← re_add_im z]
    exact Subfield.add_mem L h₁ h₂

lemma icc_L'' (z :ℂ) {c₁ c₂ : Construction.circle} (hc₁: c₁ ∈ C L) (hc₂: c₂ ∈ C L) (h_ne : c₁.points' ≠ c₂.points'): z ∈ c₁.points ∩ c₂.points ↔
  z ∈ {z | 2 * (c₂.c.re - c₁.c.re) * z.re - 2 * (c₂.c.im * I - c₁.c.im * I) * (z.im * I) = c₁.r^2- c₂.r^2-c₁.c.re^2+c₂.c.re^2 + (c₁.c.im*I)^2-(c₂.c.im*I)^2} := by
    refine ⟨?_,?_⟩ <;> intro h
    . sorry
    . sorry

lemma icc_L' (z :ℂ) {c₁ c₂ : Construction.circle} (hc₁: c₁ ∈ C L) (hc₂: c₂ ∈ C L) (h_ne : c₁.points' ≠ c₂.points'): z ∈ c₁.points ∩ c₂.points ↔
  ∃ l :line, l ∈ Construction.L L ∧  z ∈ l.points ∩ c₁.points ∧ z ∈ l.points ∩ c₂.points := by
  refine ⟨?_,?_⟩ <;> intro h
  have hc₁c : c₁.c ∈ L := by
    obtain ⟨_,_, _, _⟩ := hc₁
    simp_all only [ne_eq, Set.mem_inter_iff, SetLike.mem_coe]
  have hc₂c : c₂.c ∈ L := by
    obtain ⟨_,_, _, _⟩ := hc₂
    simp_all only [ne_eq, Set.mem_inter_iff, SetLike.mem_coe]
  have hc₁r : ↑(c₁.r ^2) ∈ L := by
    obtain ⟨_, _, _, _, _⟩ := hc₁
    simp_all only [dist_eq, ne_eq, Set.mem_inter_iff, SetLike.mem_coe, true_and, Complex.sq_abs,
      distSq_L]
  have hc₂r : ↑(c₂.r^2) ∈ L := by
    obtain ⟨_, _, _, _, _⟩ := hc₂
    simp_all only [dist_eq, ne_eq, Set.mem_inter_iff, SetLike.mem_coe, true_and, Complex.sq_abs,
      distSq_L]
  . by_cases hx: c₁.c.re = c₂.c.re
    . have: c₁.c.im ≠ c₂.c.im := by
        by_contra hy
        have h_eq: c₁.c = c₂.c := Complex.ext hx hy
        simp only [circle.points', h_eq, ne_eq, EuclideanGeometry.Sphere.mk.injEq, true_and] at h_ne
        simp only [circle.points, h_eq, Set.mem_inter_iff, mem_sphere_iff_norm, norm_eq_abs] at h
        obtain ⟨left, right⟩ := h
        simp_all only [not_true_eq_false]
      use ⟨0,1⟩
      sorry
    . by_cases hy: c₁.c.im = c₂.c.im
      . use ⟨0,1⟩
        sorry
      -- use z₁ z₂ from pdf
      . use ⟨⟨(c₁.r^2 - c₂.r^2 + c₂.c.re^2 - c₁.c.re^2 - (c₂.c.im)^2 + (c₁.c.im)^2 - 2 * (c₂.c.im  - c₁.c.im) * c₁.c.im) / (2*(c₂.c.re - c₁.c.re)),c₁.c.im⟩,⟨(c₁.r^2 - c₂.r^2 + c₂.c.re^2 - c₁.c.re^2 - (c₂.c.im)^2 + (c₁.c.im)^2 - 2 * (c₂.c.im  - c₁.c.im) * c₂.c.im) / (2*(c₂.c.re - c₁.c.re)),c₂.c.im⟩⟩
        refine ⟨?_,?_,?_⟩
        . simp [Construction.L, Construction.line, SetLike.mem_coe, ne_eq, Set.mem_setOf_eq, line.mk.injEq]
          refine ⟨⟨(c₁.r^2 - c₂.r^2 + c₂.c.re^2 - c₁.c.re^2 - (c₂.c.im)^2 + (c₁.c.im)^2 - 2 * (c₂.c.im  - c₁.c.im) * c₁.c.im) / (2*(c₂.c.re - c₁.c.re)),c₁.c.im⟩,⟨(c₁.r^2 - c₂.r^2 + c₂.c.re^2 - c₁.c.re^2 - (c₂.c.im)^2 + (c₁.c.im)^2 - 2 * (c₂.c.im  - c₁.c.im) * c₂.c.im) / (2*(c₂.c.re - c₁.c.re)),c₂.c.im⟩, ?_ , ?_ ,?_, ?_⟩
          . simp only [and_self]
          . rw[ir_im_iff_L]
            refine ⟨?_,?_⟩
            . simp only [ofReal_mul, ofReal_div, ofReal_sub, ofReal_add, ofReal_pow, ofReal_ofNat]
              refine Subfield.div_mem L ?_ ?_
              . have: ↑c₁.r ^ 2 - ↑c₂.r ^ 2 + ↑c₂.c.re ^ 2 - ↑c₁.c.re ^ 2 - ↑c₂.c.im ^ 2 + ↑c₁.c.im ^ 2 - 2 * (↑c₂.c.im - ↑c₁.c.im) * ↑c₁.c.im =
                  ↑c₁.r ^ 2 - ↑c₂.r ^ 2 + ↑c₂.c.re ^ 2 - ↑c₁.c.re ^ 2 + (c₂.c.im* Complex.I )^ 2 - (c₁.c.im * Complex.I)^ 2 + 2 * ((c₂.c.im * Complex.I) - (c₁.c.im * Complex.I)) * (c₁.c.im * Complex.I ):= by simp_rw [mul_pow, Complex.I_sq, ←sub_mul _ _ Complex.I, ←mul_assoc, mul_comm _ I, ←mul_assoc, ←pow_two, Complex.I_sq]; ring_nf
                rw[this]
                refine Subfield.add_mem L ?_ ?_
                . refine Subfield.sub_mem L ?_ ?_
                  . refine Subfield.add_mem L ?_ ?_
                    . refine Subfield.sub_mem L ?_ ?_
                      . refine Subfield.add_mem L ?_ ?_
                        . refine Subfield.sub_mem L ?_ ?_
                          . norm_cast
                          . norm_cast
                        . exact Subfield.pow_mem L (ir_L L c₂.c hc₂c) 2
                      . exact Subfield.pow_mem L (ir_L L c₁.c hc₁c) 2
                    . exact Subfield.pow_mem L (im_L L c₂.c hc₂c) 2
                  . exact Subfield.pow_mem L (im_L L c₁.c hc₁c) 2
                . refine Subfield.mul_mem L ?_ ?_
                  . refine Subfield.mul_mem L (ofNat_mem L 2) ?_
                    . exact Subfield.sub_mem L (im_L L c₂.c hc₂c) (im_L L c₁.c hc₁c)
                  . exact im_L L c₁.c hc₁c
              . refine Subfield.mul_mem L (ofNat_mem L 2) ?_
                exact Subfield.sub_mem L (ir_L L c₂.c hc₂c) (ir_L L c₁.c hc₁c)
            . exact im_L L c₁.c hc₁c
          . rw[ir_im_iff_L]
            refine ⟨?_,?_⟩
            . simp only [ofReal_mul, ofReal_div, ofReal_sub, ofReal_add, ofReal_pow, ofReal_ofNat]
              refine Subfield.div_mem L ?_ ?_
              . have: ↑c₁.r ^ 2 - ↑c₂.r ^ 2 + ↑c₂.c.re ^ 2 - ↑c₁.c.re ^ 2 - ↑c₂.c.im ^ 2 + ↑c₁.c.im ^ 2 - 2 * (↑c₂.c.im - ↑c₁.c.im) * ↑c₂.c.im =
                  ↑c₁.r ^ 2 - ↑c₂.r ^ 2 + ↑c₂.c.re ^ 2 - ↑c₁.c.re ^ 2 + (c₂.c.im* Complex.I )^ 2 - (c₁.c.im * Complex.I)^ 2 + 2 * ((c₂.c.im * Complex.I) - (c₁.c.im * Complex.I)) * (c₂.c.im * Complex.I ):= by simp_rw [mul_pow, Complex.I_sq, ←sub_mul _ _ Complex.I, ←mul_assoc, mul_comm _ I, ←mul_assoc, ←pow_two, Complex.I_sq]; ring_nf
                rw[this]
                refine Subfield.add_mem L ?_ ?_
                . refine Subfield.sub_mem L ?_ ?_
                  . refine Subfield.add_mem L ?_ ?_
                    . refine Subfield.sub_mem L ?_ ?_
                      . refine Subfield.add_mem L ?_ ?_
                        . refine Subfield.sub_mem L ?_ ?_
                          . norm_cast
                          . norm_cast
                        . exact Subfield.pow_mem L (ir_L L c₂.c hc₂c) 2
                      . exact Subfield.pow_mem L (ir_L L c₁.c hc₁c) 2
                    . exact Subfield.pow_mem L (im_L L c₂.c hc₂c) 2
                  . exact Subfield.pow_mem L (im_L L c₁.c hc₁c) 2
                . refine Subfield.mul_mem L ?_ ?_
                  . refine Subfield.mul_mem L (ofNat_mem L 2) ?_
                    . exact Subfield.sub_mem L (im_L L c₂.c hc₂c) (im_L L c₁.c hc₁c)
                  . exact im_L L c₂.c hc₂c
              . refine Subfield.mul_mem L (ofNat_mem L 2) ?_
                exact Subfield.sub_mem L (ir_L L c₂.c hc₂c) (ir_L L c₁.c hc₁c)
            . exact im_L L c₂.c hc₂c
          . rw [Complex.ext_iff, not_and_or]
            right
            simp only
            exact hy
        . simp only [Set.mem_inter_iff]
          refine ⟨?_,?_⟩
          . rw[icc_L'' L z hc₁ hc₂ h_ne] at h
            simp only [Set.mem_setOf_eq, line.points] at h ⊢
            sorry
          exact Set.mem_of_mem_inter_left h
        . simp only [Set.mem_inter_iff]
          refine ⟨?_,?_⟩
          . simp [line.points]
            sorry
          exact Set.mem_of_mem_inter_right h
  . obtain ⟨_, _ , h₁, h₂⟩ := h
    exact ⟨Set.mem_of_mem_inter_right h₁,Set.mem_of_mem_inter_right h₂⟩

example (a b c :ℝ): a = b ∧ a = c → b= c := by
  intro a_1
  obtain ⟨left, right⟩ := a_1
  subst right left
  simp_all only
