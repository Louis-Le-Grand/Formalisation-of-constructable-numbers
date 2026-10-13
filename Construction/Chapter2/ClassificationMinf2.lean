import Construction.NotMyCode.AdjuctionRootTower

open IntermediateField Construction

lemma chain_iff_adjion_roots (M : Set ℂ) (h₀ : 0 ∈ M) (h₁ : 1 ∈ M): (∃n, ∃ α: Fin n → Set ℂ, z ∈ (succ_adjion (K_zero M) n α) ∧ succ_adjion_root (K_zero M) n α) ↔  (∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (_: ∀i,  L i ≤ L (i + 1)),
    z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2)) := by
  clear h₀ h₁
  constructor
  · rintro ⟨n, α, hz, hr⟩
    have hz' := QuadraticChain.layers_le_closure (K_zero M) n α hr hz
    obtain ⟨P, hP, hzP⟩ := hz'
    obtain ⟨m, L, hmono, hzero, hlast, hdeg⟩ := hP.exists_chain
    exact ⟨m, L, hmono, hlast.symm ▸ hzP, hzero.symm, hdeg⟩
  · rintro ⟨n, L, hmono, hz, hzero, hdeg⟩
    obtain ⟨m, α, he, hr⟩ := QuadraticChain.Tower.exists_layers
      (QuadraticChain.tower_of_chain (K_zero M) n L hmono hzero hdeg)
    refine ⟨m, α, ?_, hr⟩
    rw [he] at hz
    exact hz


theorem Classfication_z_in_M_inf  (M : Set ℂ) (z : ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) : z ∈ M_inf M ↔ ∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (_: ∀i,  L i ≤ L (i + 1)),
    z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2) := by
  refine ⟨?_, ?_⟩
  . intro h
    rw [←chain_iff_adjion_roots M h₀ h₁]
    rw[ M_inf_in_M_I] at h
    obtain ⟨n, h ⟩ := h
    have: ∃ α,  M_I M n ≤ succ_adjion (K_zero M) n α ∧ succ_adjion_root (K_zero M) n α  ∧ ConjClosed (succ_adjion (K_zero M) n α) := by
      apply M_i_in_K_i _ h₀ h₁
    obtain ⟨α, h', hr, _⟩ := this
    refine ⟨n, α,  h' h, hr⟩
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

section --! Should be in Mathlib
variable {E : Type*} [Field E] {F : Type*} [Field F] [Algebra E F]
variable {L: IntermediateField E F} [FiniteDimensional E L]
lemma IsIntegral_of_mem_finte (x : F) (hx : x ∈ L) : IsIntegral E x := by
  have: ∃ xl:L, ↑xl = x := CanLift.prf x hx
  obtain ⟨xl, hxl⟩ := this
  have : IsIntegral L x := by
    unfold IsIntegral RingHom.IsIntegralElem
    refine ⟨minpoly L xl, ?_, ?_⟩
    . rw [minpoly.eq_X_sub_C']
      exact Polynomial.monic_X_sub_C xl
    . rw [minpoly.eq_X_sub_C']
      simp only [← hxl, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
        IntermediateField.algebraMap_apply, sub_self]
  exact isIntegral_trans _ this
end

section  --! Should be in Mathlib
open FiniteDimensional
variable {E : Type*} [Field E] {F : Type*} [Field F] [Algebra E F]
variable {L K : IntermediateField E F}
lemma finrank_div  (h: L ≤ K): finrank E L ∣ finrank E K := by
  rw [dvd_iff_exists_eq_mul_left]
  use (finrank L (extendScalars h))
  rw[mul_comm]
  symm
  exact finrank_mul_finrank E ↥L ↥(extendScalars h)
end

lemma div_two_2pown (a n : ℕ) (h: a ∣ 2^ n) :  ∃m : ℕ, 2^m  = a:= by
  obtain h' := Nat.Prime.primeFactorsList_pow Nat.prime_two n
  obtain h'' := Nat.primeFactorsList_subset_of_dvd h (Ne.symm (NeZero.ne' (2 ^ n)))
  rw[h'] at h''
  have: a ≠ 0 := by
    intro ha
    simp_all only [zero_dvd_iff, pow_eq_zero_iff']
  use (a.primeFactorsList.length)
  symm
  apply Nat.eq_prime_pow_of_unique_prime_dvd this
  intro d hd da
  rw[←Nat.mem_primeFactorsList_iff_dvd this hd] at da
  have: d ∈ List.replicate n 2 := h'' da
  simp_all only [List.mem_replicate]


lemma div_two_2pown' (a n : ℕ) (h: a ∣ 2^ n) :  ∃m : ℕ, a = 2^m:= by
  obtain ⟨m, hm⟩ := div_two_2pown a n h
  exact ⟨m, Eq.symm hm⟩


lemma mulfinrank_help (R K L: IntermediateField ℚ ℂ) (h₁: R ≤ K) (h₂: K ≤ L) : FiniteDimensional.finrank R (extendScalars h₁) *
    FiniteDimensional.finrank (extendScalars h₁) (extendScalars h₂) = FiniteDimensional.finrank R (extendScalars (Trans.trans h₁ h₂)) := by
  rw [←IntermediateField.relfinrank_eq_finrank_of_le h₁,
  ←IntermediateField.relfinrank_eq_finrank_of_le (Trans.trans h₁ h₂),
  ←IntermediateField.relfinrank_mul_relfinrank h₁ h₂]
  have: FiniteDimensional.finrank ↥(extendScalars h₁) ↥(extendScalars h₂) = K.relfinrank L := by
    exact Eq.symm (relfinrank_eq_finrank_of_le h₂)
  simp only [mul_eq_mul_left_iff, this]

lemma degree_of_Ln (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (h:  ∃   (_: ∀i,  L i ≤ L (i + 1)),
    K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2)): relfinrank (K_zero M) (L n) = 2^n := by
  obtain ⟨hL, hL0, h_degree⟩ := h
  have: K_zero M ≤ L n := by
    rw[hL0]
    exact monotone_nat_of_le_succ (fun n ↦ hL n) (Nat.zero_le n)
  induction n
  case zero => simp only [hL0, relfinrank_self, pow_zero]
  case succ n Ih =>
    rw[relfinrank_eq_finrank_of_le this]
    have hn: K_zero M ≤ L n := by
      rw[hL0]
      exact monotone_nat_of_le_succ (fun n ↦ hL n) (Nat.zero_le n)
    obtain h_degree' := h_degree n (by linarith)
    specialize hL n
    rw[pow_succ, ←Ih ?_ hn, relfinrank_eq_finrank_of_le hn, ←h_degree', relfinrank_eq_finrank_of_le hL]
    symm
    have: FiniteDimensional.finrank ↥(L n) ↥(extendScalars hL) = FiniteDimensional.finrank ↥(extendScalars hn) ↥(extendScalars hL) := by norm_cast
    rw[this]
    exact mulfinrank_help (K_zero M) (L n) (L (n + 1)) hn hL
    intro i hi
    rw[h_degree i ]
    exact Nat.lt_add_right 1 hi


lemma Classfication_z_in_M_inf_2m {M : Set ℂ} (h₀: 0 ∈ M) (h₁:1 ∈ M) (z : ℂ) :
  z ∈ M_inf M →  ∃ (m : ℕ) ,((2  : ℕ) ^ m) = Polynomial.degree (minpoly (K_zero M) z)  := by
  intro h
  rw[Classfication_z_in_M_inf M z h₀ h₁] at h
  obtain ⟨n, L, hL, hLn, hL0, h_degree⟩ := h
  have: K_zero M ≤ L n := by
    rw[hL0]
    exact monotone_nat_of_le_succ (fun n ↦ hL n) (Nat.zero_le n)
  have hn: relfinrank (K_zero M) (L n) = 2^n := by
    exact degree_of_Ln n L ⟨hL, hL0, h_degree⟩
  rw[relfinrank_eq_finrank_of_le this] at hn
  have hm: ∃m, FiniteDimensional.finrank (K_zero M) ((K_zero M) ⟮z⟯) = 2^m := by
    have : FiniteDimensional.finrank (K_zero M) ((K_zero M) ⟮z⟯) ∣ 2^n := by
      rw[←hn]
      apply finrank_div
      simp only [adjoin_le_iff, coe_extendScalars, Set.le_eq_subset, Set.singleton_subset_iff,
        SetLike.mem_coe, hLn]
    apply div_two_2pown' _  _ this
  have: IsIntegral (↥(K_zero M)) z := by
    have _: FiniteDimensional (↥(K_zero M)) (extendScalars this) := by
      apply FiniteDimensional.of_finrank_pos
      rw[hn]
      simp only [Nat.ofNat_pos, pow_pos]
    have: z ∈ (extendScalars this) := by
      simp_all only [mem_extendScalars]
    apply IsIntegral_of_mem_finte z this
  obtain ⟨m, hm⟩ := hm
  use m
  rw[Polynomial.degree_eq_natDegree (minpoly.ne_zero this), ← IntermediateField.adjoin.finrank this]
  symm
  norm_cast at hm ⊢

lemma Classfication_z_in_M_inf_2m_not {M : Set ℂ} (h₀: 0 ∈ M) (h₁:1 ∈ M) (z : ℂ) :
    ¬ (∃ m ,2 ^ m = (minpoly (K_zero M) z).degree) → z ∉ M_inf M := by
  apply Not.imp_symm
  simp only [not_not, Nat.cast_ofNat]
  apply Classfication_z_in_M_inf_2m (h₀: 0 ∈ M) (h₁:1 ∈ M)


lemma Classfication_z_in_M_inf_2m_rat {M : Set ℂ} (h₀: 0 ∈ M) (h₁:1 ∈ M) (z : ℂ) (h: ∃j:ℕ, FiniteDimensional.finrank ℚ (K_zero M) = 2^j) :
    ¬ (∃ m, 2 ^ m = (minpoly ℚ z).degree) → z ∉ M_inf M := by
  apply Not.imp_symm
  simp only [not_not, Nat.cast_ofNat]
  have:  (∃ m ,2 ^ m = (minpoly (K_zero M) z).degree) → ∃ m, 2 ^ m = (minpoly ℚ z).degree := by
    intro h'
    obtain ⟨m, hm⟩ := h'
    obtain ⟨j, hj⟩ := h
    have hmj: FiniteDimensional.finrank ℚ (restrictScalars ℚ ((K_zero M) ⟮z⟯)) = 2^(m+j) := by
      have: minpoly (↥(K_zero M)) z ≠ 0 := by
        apply Polynomial.zero_le_degree_iff.mp
        rw[←hm]
        simp only [Nat.ofNat_nonneg, pow_nonneg]
      rw[Polynomial.degree_eq_natDegree this] at hm
      norm_cast at hm
      rw[pow_add, ←hj, hm,  ← IntermediateField.adjoin.finrank, mul_comm]
      symm
      apply FiniteDimensional.finrank_mul_finrank
      . by_contra h
        have: minpoly (↥(K_zero M)) z = 0:= minpoly.eq_zero h
        contradiction
    have hdiv: FiniteDimensional.finrank ℚ ℚ⟮z⟯ ∣ FiniteDimensional.finrank ℚ (restrictScalars ℚ ((K_zero M) ⟮z⟯)) := by
      apply finrank_div
      rw [restrictScalars_adjoin]
      apply IntermediateField.adjoin.mono
      exact Set.subset_union_right
    have: IsIntegral ℚ z := by
      have: FiniteDimensional ℚ ↥(restrictScalars ℚ (↥(K_zero M))⟮z⟯) := by
        apply FiniteDimensional.of_finrank_pos
        rw[hmj]
        simp only [Nat.ofNat_pos, pow_pos]
      have: z ∈ (restrictScalars ℚ (↥(K_zero M))⟮z⟯) := by
        rw[restrictScalars_adjoin]
        apply IntermediateField.subset_adjoin
        exact Set.mem_union_right _ rfl
      apply IsIntegral_of_mem_finte z this
    rw[hmj, IntermediateField.adjoin.finrank this] at hdiv --dvd_iff_exists_eq_mul_left
    rw[Polynomial.degree_eq_natDegree (minpoly.ne_zero this)]
    norm_cast
    exact div_two_2pown ((minpoly ℚ z).natDegree) (m+j) hdiv
  exact fun h' => this ((Classfication_z_in_M_inf_2m h₀ h₁ z) h')
