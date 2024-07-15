import Construction.Chapter1.def

open Construction

/-
# M in ICL(M)
-/
lemma M_in_ICL_M (M : Set ℂ) : M ⊆ ICL_M M := by
  intro x hx
  left; left; left
  exact hx

/-
# M_I Monotone
 i.e. `M_I M n ⊆ M_I M (n+1)`
-/
lemma M_I_Monotone (M : Set ℂ) : ∀n, M_I M n ⊆ M_I M (n+1) := by
  intro n
  exact M_in_ICL_M (M_I M n)

/-
# M in M_I
Now we can deduce that `M ⊆ M_I M n` for all `n`
-/
lemma M_in_M_I (M : Set ℂ) : ∀n, M ⊆ M_I M n := by
  intro n
  induction n
  simp only [M_I]
  exact fun ⦃a⦄ a => a
  case succ n hn =>
    exact le_trans hn (M_I_Monotone M n)

/-
# M_I in M_inf
-/
lemma M_I_in_M_inf (M : Set ℂ)(m: ℕ): M_I M m ⊆ M_inf M := by
  exact Set.subset_iUnion_of_subset m fun ⦃a⦄ a => a -- Unfold, exact?

/-
# M_I in M_inf for an element
Combining the previous two lemmas we can deduce that `x ∈ M_I M m ↔ x ∈ M_inf M`
-/
lemma M_M_inf (M : Set ℂ) : M ⊆ M_inf M := by
  exact M_I_in_M_inf M 0
