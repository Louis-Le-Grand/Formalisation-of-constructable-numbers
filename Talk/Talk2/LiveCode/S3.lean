import Construction.Chapter1.def

open Construction

/-
# M in ICL(M)
-/
lemma M_in_ICL_M (M : Set ℂ) : M ⊆ ICL_M M := by
  sorry

/-
# M_I Monotone
 i.e. `M_I M n ⊆ M_I M (n+1)`
-/
lemma M_I_Monotone (M : Set ℂ) : ∀n, M_I M n ⊆ M_I M (n+1) := by
  sorry

/-
# M in M_I
Now we can deduce that `M ⊆ M_I M n` for all `n`
-/
lemma M_in_M_I (M : Set ℂ) : ∀n, M ⊆ M_I M n := by
  sorry

/-
# M_I in M_inf
-/
lemma M_I_in_M_inf (M : Set ℂ)(m: ℕ): M_I M m ⊆ M_inf M := by
  sorry

/-
# M_I in M_inf for an element
Combining the previous two lemmas we can deduce that `x ∈ M_I M m ↔ x ∈ M_inf M`
-/
lemma M_M_inf (M : Set ℂ) : M ⊆ M_inf M := by
  sorry
