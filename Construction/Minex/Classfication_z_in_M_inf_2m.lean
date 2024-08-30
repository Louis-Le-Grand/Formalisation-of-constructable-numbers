import Construction.Chapter2.KZero
import Construction.NotMyCode.PR14987

section pre
open IntermediateField Construction

theorem Classfication_z_in_M_inf  (M : Set ℂ) (z : ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) : z ∈ M_inf M ↔ ∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (_: ∀i,  L i ≤ L (i + 1)),
    z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2) := by sorry

end pre

open IntermediateField Construction

lemma Classfication_z_in_M_inf_2m {M : Set ℂ} (h₀: 0 ∈ M) (h₁:1 ∈ M) (z : ℂ) :
  z ∈ M_inf M →  ∃ (m : ℕ) ,((2  : ℕ) ^ m) = Polynomial.degree (minpoly (K_zero M) z)  := by sorry
