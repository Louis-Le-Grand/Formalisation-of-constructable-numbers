import Construction.Chapter2.MField
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.Norm

open Construction

noncomputable def K_zero (M : Set ℂ) : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ (M ∪ conj_set M)

variable {F: Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

lemma K_le_K_adjion (K : IntermediateField F E) (M : Set E) ( x : E) (hx: x ∈ K) : x ∈ IntermediateField.adjoin K M := by
    unfold IntermediateField.adjoin
    apply Subfield.subset_closure
    apply Or.inl
    simp [hx]

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
      exact K_le_K_adjion K M x hx
    rw [@Set.Subset.antisymm_iff]
    constructor
    sorry
    sorry




open IntermediateField
variable (K : IntermediateField F E) (L : IntermediateField K E)


theorem dergree_two_eq_sqr :  FiniteDimensional.finrank K L = 2 ↔ ∃ x : E, x ^ 2 ∈ K ∧ ¬(x ∈ K) ∧ L = IntermediateField.adjoin K {x} := by
  refine Iff.intro ?_ ?_
  intros h
  sorry
  intros h
  obtain ⟨x, hx, hx', hlk⟩ := h
  rw[hlk]
  rw[IntermediateField.adjoin.finrank]
  have : ∃ z : K, z = x ^ 2 := by
    simp only [Subtype.exists, exists_prop, exists_eq_right, hx]
  obtain ⟨z, hz⟩ := this
  let p := Polynomial.X ^ 2 - Polynomial.C z
  have : minpoly (↥K) x = p := by
    refine (minpoly.eq_of_irreducible_of_monic ?hp1 ?hp2 ?hp3).symm
    . sorry
    . simp only [map_sub,
        map_pow,
        Polynomial.aeval_X,
        Polynomial.aeval_C,
        IntermediateField.algebraMap_apply,
        sub_self,
        p, hz]
    . refine Polynomial.monic_X_pow_sub_C z ?hp3.h
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  rw[this]
  exact Polynomial.natDegree_X_pow_sub_C
  sorry
