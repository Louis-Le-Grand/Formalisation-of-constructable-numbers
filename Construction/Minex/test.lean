import Mathlib
import Construction.Chapter2.KZero

lemma dim_k_zero_ang: ∃ j:ℕ, FiniteDimensional.finrank ℚ ↥(K_zero {0, 1, Complex.exp (Complex.I * ↑Real.pi / 3)}) = (2 ^ j) := by
  use 1
  simp [K_zero,conj_set]

  sorry
