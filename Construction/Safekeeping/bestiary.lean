import Construction.Safekeeping.joshua
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Irrational
--import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.SpecificDegree
import Construction.NotMyCode.map_of_isScalarTower
--import Mathlib.RingTheory.IntegralClosure

open Complex Construction



lemma Classfication_z_in_M_inf_2m (M : Set ℂ) (z : ℂ) :
  z ∈ M_inf M →  ∃ (m : ℕ) ,((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z)  := by
    sorry
    -- intro h
    -- rw [Classfication_z_in_M_inf] at h
    -- obtain ⟨n, L, H, h₁, h₂, h₃⟩ := h
    -- have: IsIntegral (↥(K_zero M)) z := by sorry --apply IsIntegral.of_finite (K_zero M) (L n)
    -- rw[Polynomial.degree_eq_natDegree]
    -- rw[←IntermediateField.adjoin.finrank _]
    -- rw[h₂]
    -- have h: ∃ j:ℕ, z ∈ L j ∧ z ∉ L (j-1) := by
    --   sorry
    -- obtain ⟨j, hj, _⟩ := h
    -- sorry
    -- exact this
    -- exact minpoly.ne_zero this

lemma short (M : Set ℂ) (z : ℂ) :
  ¬ (∃ (m : ℕ) ,((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z)) → z ∉ M_inf M := by
    apply Not.imp_symm
    simp
    apply Classfication_z_in_M_inf_2m
