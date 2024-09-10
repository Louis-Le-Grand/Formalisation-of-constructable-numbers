import Mathlib.FieldTheory.Adjoin
import Mathlib.Data.Complex.Module
import Mathlib.Algebra.Star.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic


noncomputable section PR14987
open IntermediateField FiniteDimensional

universe u v w

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable (A B C : IntermediateField F E)

namespace IntermediateField

def relrank := Module.rank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))

def relfinrank := finrank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))

variable {A B C}

theorem relfinrank_eq_finrank_of_le (h : A ≤ B) : relfinrank A B = finrank A (extendScalars h) := sorry

theorem relfinrank_self : relfinrank A A = 1 := by sorry
end IntermediateField
end PR14987

section pre

def conj_set (M : Set ℂ) : Set ℂ := {starRingEnd ℂ z | z ∈ M}

noncomputable def K_zero (M : Set ℂ) : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ (M ∪ conj_set M)

end pre

open IntermediateField

example (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (h:  ∃   (_: ∀i,  L i ≤ L (i + 1)),
    z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2)): relfinrank (K_zero M) (L n) = 2^n := by
    obtain ⟨hL, hLn, hL0, h_degree⟩ := h
    have: K_zero M ≤ L n := by sorry
    induction n
    case zero => simp only [hL0, relfinrank_self, pow_zero]
    case succ n Ih =>
      rw[relfinrank_eq_finrank_of_le this]
      have hn: K_zero M ≤ L n := by
        rw[hL0]
        exact monotone_nat_of_le_succ (fun n ↦ hL n) (Nat.zero_le n)
      specialize h_degree n (by linarith)
      specialize hL n
      --rw[pow_succ, ←Ih, relfinrank_eq_finrank_of_le hn, ←h_degree, relfinrank_eq_finrank_of_le hL]
      --rw [FiniteDimensional.finrank_mul_finrank]
      sorry
