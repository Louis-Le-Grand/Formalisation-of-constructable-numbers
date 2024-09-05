import Construction.Chapter2.ClasificationMinf

open IntermediateField Construction
lemma test (M : Set ℂ) (_: 0 ∈ M) (_:1 ∈ M) (n : ℕ) : ∃ α: Fin n → Set ℂ, M_I M n ≤ (succ_adjion (K_zero M) n α) ∧ succ_adjion_root (K_zero M) n α ∧ ConjClosed (succ_adjion (K_zero M) n α) := by
    sorry

theorem Classfication_z_in_M_inf  (M : Set ℂ) (z : ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) : z ∈ M_inf M ↔ ∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (_: ∀i,  L i ≤ L (i + 1)),
    z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2) := by
  refine ⟨?_, ?_⟩
  . sorry
  intro h
  obtain ⟨n, L, h, hz, hL₀, h_deg⟩ := h
  have hLn: (L n).carrier ≤ MField M h₀ h₁ := by
    apply adjoin_in_MField' M h₀ h₁ L h hL₀ n h_deg
  simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring, coe_toSubalgebra,
    Set.le_eq_subset, Set.subset_def, SetLike.mem_coe] at hLn
  simp_rw[ ←Subfield.mem_carrier] at hLn
  have : (MField M h₀ h₁).carrier = M_inf M := rfl
  rw[this] at hLn
  simp[hLn, hz]
