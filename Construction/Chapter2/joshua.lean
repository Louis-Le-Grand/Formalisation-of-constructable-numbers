import Construction.Chapter2.MField
import Mathlib.FieldTheory.Adjoin

open Construction

noncomputable def K_zero (M : Set ℂ) : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ (M ∪ conj_set M)

lemma conj_adjion (K : IntermediateField ℚ ℂ) [ConjClosed K] (M : Set ℂ) [ConjClosed M] :
    ConjClosed (IntermediateField.adjoin K M) where
  equal := by
    have h₁ : conj_set M ⊆ IntermediateField.adjoin K M := by
      rw[←@ConjClosed.equal M]
      exact IntermediateField.subset_adjoin K M
    have h₂ : conj_set K ⊆ IntermediateField.adjoin K M := by
      rw[←@ConjClosed.equal K, @Set.subset_def]
      intro x hx
      refine SetLike.mem_coe.mpr ?_
      sorry
    rw [@Set.Subset.antisymm_iff]
    constructor
    sorry
    sorry


open IntermediateField
variable (K L : IntermediateField ℚ ℂ) [Module K L]

-- theorem dergree_two_eq_sqr :  FiniteDimensional.finrank K L = 2 ↔
--     ∃ w : K, (w:ℂ)^(1/2:ℂ) ∉ K ∧ L = K⟮(w:ℂ)^(1/2:ℂ)⟯ := by sorry
