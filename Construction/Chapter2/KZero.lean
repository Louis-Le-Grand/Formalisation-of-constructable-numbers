import Construction.Chapter2.MField


open Construction

noncomputable def K_zero (M : Set ℂ) : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ (M ∪ conj_set M)


lemma M_K_zero (M : Set ℂ) : M ⊆ ↑(K_zero M) := by
  exact le_trans (b:= (M ∪ conj_set M)) (Set.le_iff_subset.mpr Set.subset_union_left) (IntermediateField.adjoin_le_iff.mp fun ⦃x⦄ a ↦ a)


lemma K_zero_eq_rational_if_M_sub_Q (M : Set ℂ) (h : M ⊆ Set.range ((↑): ℚ → ℂ)) : K_zero M = ⊥ := by
  apply le_antisymm
  . apply IntermediateField.adjoin_le_iff.mpr
    simp
    constructor
    exact h
    have h': ∀ z ∈ M ,  (starRingEnd ℂ) z = z := by
      intro m hm; rw[Complex.conj_eq_iff_im]
      apply h at hm; simp at hm
      obtain ⟨q, hq⟩ := hm
      rw[←hq]
      simp
    intro y hy
    obtain ⟨q, hq₁, hq₂⟩ := hy
    rw[←hq₂, h']
    exact h hq₁
    exact hq₁
  . simp



lemma K_le_K_adjion {F: Type*} [Field F] {E : Type*} [Field E] [Algebra F E] (K : IntermediateField F E) (M : Set E) ( x : E) (hx: x ∈ K) : x ∈ IntermediateField.adjoin K M := by
    unfold IntermediateField.adjoin
    apply Subfield.subset_closure
    apply Or.inl
    simp [hx]


lemma conj_adjion (K : IntermediateField ℚ ℂ) [ConjClosed K] (M : Set ℂ) [ConjClosed M] :
    ConjClosed (IntermediateField.adjoin K M) where
  equal := by
    have h₁ : M ⊆  conj_set (IntermediateField.adjoin K M) := by
      nth_rw 1 [@ConjClosed.equal M]
      apply ConjClosed.conj_inclusion (IntermediateField.subset_adjoin K M)
    have h₂ :  ↑K ⊆ conj_set (IntermediateField.adjoin K M) := by
      rw[@ConjClosed.equal K]
      apply ConjClosed.conj_inclusion
      rw [@Set.subset_def]
      intro x hx
      refine SetLike.mem_coe.mpr ?_
      exact K_le_K_adjion K M x hx
    have: ↑(IntermediateField.adjoin (↥K) M) ⊆  conj_set ↑(IntermediateField.adjoin (↥K) M) := by
      suffices h : (IntermediateField.adjoin K M).carrier ⊆ (ConjClosed.conj_field (IntermediateField.toSubfield (IntermediateField.adjoin K M))) by{
        simp [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
        IntermediateField.coe_toSubalgebra, ConjClosed.conj_field, Set.subset_def, Subfield.mem_carrier] at h
        rw[Set.subset_def]
        apply h
      }
      simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
        IntermediateField.coe_toSubalgebra]
      apply IntermediateField.adjoin_le_subfield
      . intro x hx
        simp_all only [Set.mem_range, IntermediateField.algebraMap_apply, Subtype.exists,
          exists_prop, exists_eq_right, SetLike.mem_coe]
        apply h₂
        simp_all only [SetLike.mem_coe]
      exact h₁
    rw[Set.Subset.antisymm_iff]
    refine ⟨this, ?_ ⟩
    nth_rw 2 [←conj_conj_id ↑(IntermediateField.adjoin (↥K) M)]
    apply ConjClosed.conj_inclusion this


lemma conj_adjion' {K : IntermediateField ℚ ℂ} (E : IntermediateField K ℂ) [ConjClosed E] (M : Set ℂ) [ConjClosed M] :
    ConjClosed (IntermediateField.adjoin E M) := by
    have : ConjClosed (IntermediateField.adjoin (IntermediateField.restrictScalars ℚ E) M) := by
      exact @conj_adjion (IntermediateField.restrictScalars ℚ E) (ConjClosed.conj_restrict E) M _
    exact this


lemma K_zero_conjectClosed (M : Set ℂ) : ConjClosed (K_zero M) := by
  have : K_zero M = IntermediateField.restrictScalars ℚ (IntermediateField.adjoin (⊥: IntermediateField ℚ ℂ) (M ∪ conj_set M)) := by
    rw [IntermediateField.restrictScalars_adjoin]
    unfold K_zero
    have a: IntermediateField.adjoin ℚ (M ∪ conj_set M) ≤ IntermediateField.adjoin ℚ ((⊥: (IntermediateField ℚ ℂ)) ∪ (M ∪ conj_set M)) := by
      apply IntermediateField.adjoin.mono
      simp only [Set.bot_eq_empty, Set.empty_union, Set.union_subset_iff, Set.subset_union_left,
        Set.subset_union_right, and_self]
    have b: IntermediateField.adjoin ℚ ((⊥: (IntermediateField ℚ ℂ)) ∪ (M ∪ conj_set M)) ≤ IntermediateField.adjoin ℚ (M ∪ conj_set M) := by
      apply IntermediateField.adjoin_le_iff.mpr
      simp only [Set.le_eq_subset, Set.union_subset_iff]
      refine ⟨?_, ?_, ?_ ⟩
      norm_cast; exact OrderBot.bot_le (IntermediateField.adjoin ℚ (M ∪ conj_set M))
      exact IntermediateField.subset_adjoin_of_subset_right _ _ (Set.le_iff_subset.mpr Set.subset_union_left)
      exact IntermediateField.subset_adjoin_of_subset_right _ _ (Set.le_iff_subset.mpr Set.subset_union_right)
    refine (IntermediateField.ext ?_).symm
    intro x
    refine ⟨fun a_1 ↦ b (a (b a_1)), fun a_1 ↦ a (b (a a_1))⟩
  rw[this]
  apply @conj_adjion ⊥ ConjClosed.Rat_ConjClosed' (M ∪ conj_set M) (ConjClosed.M_con_M M)


lemma K_zero_in_MField (M : Set ℂ)(h₀: 0 ∈ M)(h₁:1 ∈ M): K_zero M ≤ @Subfield.toIntermediateField ℚ ℂ _ _ _ (MField M h₀ h₁) (fun x ↦ SubfieldClass.ratCast_mem (MField M h₀ h₁) x)  := by
  apply IntermediateField.adjoin_le_iff.mpr
  simp only [Set.le_eq_subset, Set.union_subset_iff]
  refine ⟨ ?_, ?_ ⟩
  . rw [Set.subset_def]
    intro x hx
    apply IntermediateField.mem_carrier.mp
    unfold MField Subfield.toIntermediateField
    dsimp
    apply M_M_inf
    exact hx
  . rw [Set.subset_def]
    intro x hx
    apply IntermediateField.mem_carrier.mp
    unfold MField Subfield.toIntermediateField
    dsimp
    have : (starRingEnd ℂ ) x ∈ M := by
      simp only [conj_set, Set.mem_setOf_eq] at hx
      obtain ⟨a, ha, hx⟩ := hx
      rw [←hx]
      simp
      exact ha
    have : (starRingEnd ℂ ) ((starRingEnd ℂ ) x) ∈ M_inf M := by
      apply conj_M_Inf _ h₀ h₁
      apply M_M_inf
      exact this
    simp only [RingHomCompTriple.comp_apply, RingHom.id_apply] at this
    exact this
