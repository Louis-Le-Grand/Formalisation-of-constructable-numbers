import Construction.Chapter2.KZero
import Construction.NotMyCode.PR14987

open IntermediateField Construction

lemma adjoin_in_MField' (M : Set ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) (L : ℕ →  IntermediateField ℚ ℂ) (h: ∀i,  L i ≤ L (i + 1)) (hL₀: K_zero M = L 0) (n: ℕ) (h_deg: ∀ i < n, relfinrank (L i) (L (i+1)) = 2) : (L n).carrier ≤ MField M h₀ h₁ := by sorry


section test

variable {E : Type*} [Field E] {F : Type*} [Field F] [Algebra E F]


def succ_adjion (K: IntermediateField E F) (n : ℕ) (α: Fin n → Set F) := IntermediateField.adjoin K (⋃ i, α  i)

lemma succ_adjion_le (K: IntermediateField E F) (n m: ℕ) (αn: Fin n  → Set F) (αm: Fin m → Set F) : succ_adjion K n αn ≤ succ_adjion K (n+m) (Fin.append αn αm) := by
  unfold succ_adjion
  apply IntermediateField.adjoin.mono
  simp only [Set.iUnion_subset_iff]
  intro i
  rw [Set.subset_def]
  intro x
  simp only [Set.mem_iUnion]
  intro h
  use Fin.castAdd m i
  simp only [Fin.append_left, h]

def SetOfRoots (K : IntermediateField E F) (M : Set F) := ∀ x : F, x ∈ M →   x * x ∈ K --∧ ¬(x ∈ K)

def succ_adjion_root  (K: IntermediateField E F) (n : ℕ) (α: Fin n → Set F) := ∀ i, SetOfRoots (IntermediateField.adjoin K (⋃ (j : Fin n), ⋃ (_ : j < i), α j)) (α i)

lemma succ_adjion_root_split  (K: IntermediateField E F) (n : ℕ) (α: Fin n → Set F) (h : succ_adjion_root K n α) (α₁: Fin 1 → Set F) : SetOfRoots (IntermediateField.adjoin K (⋃  i, α i)) (α₁ 1) →  succ_adjion_root K (n+1) (Fin.append α α₁) := by
  intro h1 i
  by_cases hin: ↑i <  n
  . unfold succ_adjion_root at h
    specialize h (Fin.castLE hin (Fin.last ↑i))
    have: (Fin.append α α₁ i) = α (Fin.castLE hin (Fin.last ↑i)) := by
      simp only [Fin.append, Fin.castLE, hin, Fin.last, Fin.addCases]
      rfl
    rw[←this] at h
    have (j: Fin n) (_: j < Fin.castLE hin (Fin.last ↑i)): α j = (Fin.append α α₁) j := by
      simp only [Fin.append, Fin.addCases, Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.is_lt,
        ↓reduceDIte, Fin.castLT_castSucc]
    have (j: Fin (n)) : ⋃ (_ : j < Fin.castLE hin (Fin.last ↑i)), α j = ⋃ (_ : j < i), Fin.append α α₁ j := by
      simp_all only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Fin.isValue, Nat.succ_eq_add_one, Fin.coe_eq_castSucc]
      apply Eq.refl
    have: (⋃ j, ⋃ (_ : j < Fin.castLE hin (Fin.last ↑i)), α j) = (⋃ j, ⋃ (_ : j < i), Fin.append α α₁ j) := by
      simp_all only [Nat.succ_eq_add_one]
      norm_cast
      rw [Set.ext_iff]
      intro x
      refine ⟨?_, ?_⟩<;> intro h
      . simp_all only [Fin.coe_eq_castSucc, Set.mem_iUnion, exists_prop]
        obtain ⟨w, h⟩ := h
        obtain ⟨left, right⟩ := h
        apply Exists.intro
        · apply And.intro
          on_goal 2 => {exact right}
          simp_all only [Fin.isValue]
      . obtain ⟨sj,⟨j, hsj⟩, hj'⟩ := h
        by_cases h: j < n
        . simp_all only [Fin.coe_eq_castSucc, Nat.succ_eq_add_one, Fin.natCast_eq_last, Set.mem_iUnion, exists_prop]
          rw [←hsj] at hj'
          refine ⟨Fin.castLE h j, ?_, ?_⟩
          . aesop
          . aesop
        . have: i < (j:ℕ) := by aesop
          have: ¬ (j < i) := by
            rw [not_lt_iff_eq_or_lt]
            right
            aesop
          simp only [this, Set.iUnion_of_empty] at hsj
          rw[←hsj] at hj'
          exfalso
          exact hj'
    rw[this] at h
    exact h
  . have: i = n := by
      rw [@Fin.le_antisymm_iff]
      refine ⟨?_, ?_ ⟩
      . apply Nat.le_of_lt_succ
        simp only [Fin.natCast_eq_last, Fin.val_last, Nat.succ_eq_add_one, Fin.is_lt]
      . rw [Nat.not_lt_eq] at hin
        unfold instLEFin
        simp only [Fin.natCast_eq_last, Fin.val_last, hin]
    rw[this]
    have: (Fin.append α α₁ ↑n) = (α₁ 1) := by
      have (x : Fin 1): x = 1:= by exact Subsingleton.eq_one x
      simp only [Fin.append, Fin.addCases, Fin.natCast_eq_last, Fin.val_last, lt_self_iff_false,
        ↓reduceDIte, Fin.val_natCast, this, Fin.isValue, eq_rec_constant]
    rw[this]
    have: (⋃ i, α i) = (⋃ j, ⋃ (_ : j < ↑n), Fin.append α α₁ j) := by
      simp_all only [Nat.succ_eq_add_one]
      rw [Set.ext_iff]
      intro x
      refine ⟨?_, ?_⟩<;> intro h
      . obtain ⟨sj, ⟨j, hsj⟩, hj'⟩ := h
        simp only [Fin.natCast_eq_last, Set.mem_iUnion, exists_prop]
        refine ⟨j, ?_, ?_⟩
        . norm_cast
          exact Fin.castSucc_lt_last j
        . rw[←hsj] at hj'
          simp only [Fin.natCast_eq_last, Fin.val_last] at hj'
          have: j < n := by exact Fin.castSucc_lt_last j
          unfold Fin.append Fin.addCases
          simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc, this, ↓reduceDIte, Fin.castLT_castSucc, hj']
      . simp only [Fin.natCast_eq_last, Set.mem_iUnion, exists_prop] at h
        obtain ⟨j, hj, hj'⟩ := h
        simp only [Set.mem_iUnion]
        refine ⟨Fin.castLE hj j, ?_⟩
        have: ↑j < n := by aesop
        simp [this, Fin.append, Fin.addCases] at hj'
        simp_all only [Fin.isValue, Fin.natCast_eq_last, Fin.val_last, lt_self_iff_false, not_false_eq_true, Nat.succ_eq_add_one]
        exact hj'
    rw[←this]
    exact h1


--! Should be in Lean
lemma split_union_fin (n m: ℕ) (α₁ : Fin n → Set ℂ) (α₂ : Fin m → Set ℂ): ⋃ i, Fin.append α₁ α₂ i = (⋃ i, α₁ i) ∪ ⋃ i, α₂ i := by
  ext x
  refine ⟨?_, ?_⟩
  . intro h
    obtain ⟨M, hM, hx⟩ := h
    obtain ⟨i, hi⟩ := hM
    simp_all only [Set.mem_iUnion, Set.mem_union]
    by_cases h: i < n
    . left
      use Fin.castLE h (Fin.last ↑i)
      rw [←hi] at hx
      have : α₁ (Fin.castLE h (Fin.last ↑i)) = Fin.append α₁ α₂ i := by
        simp only [h, ↓reduceDIte, Fin.append, Fin.castLE, Fin.last, Fin.addCases]
        rfl
      rw[this]
      exact hx
    . right
      have h' : i - n < m := by
        rw [Nat.not_lt_eq] at h
        rw [Nat.sub_eq_max_sub]
        simp only [ge_iff_le, h, max_eq_left]
        rw [propext (Nat.sub_lt_iff_lt_add' h), add_comm m n]
        exact i.2
      use Fin.castLE h' (Fin.last (i-n))
      have : α₂ (Fin.castLE h' (Fin.last (i-n))) = Fin.append α₁ α₂ i := by
        simp only [Fin.castLE, Nat.succ_eq_add_one, Fin.last, Fin.append, Fin.addCases, h,
          ↓reduceDIte, eq_rec_constant]
        rfl
      rw[← hi, ← this] at hx
      apply hx
  . intro h
    simp_all only [Set.mem_iUnion, Set.mem_union, exists_or]
    cases h
    . rename_i h
      obtain ⟨i, hi⟩ := h
      use Fin.castAdd m i
      simp only [Fin.append_left, hi]
    . rename_i h
      obtain ⟨i, hi⟩ := h
      use Fin.natAddEmb n i
      simp only [Fin.natAddEmb_apply, Fin.append_right, hi]

def K_root (K : IntermediateField E F): Set F := {x : F | x * x ∈ K}

end test

lemma test' (M : Set ℂ) (_: 0 ∈ M) (_:1 ∈ M) (n : ℕ) : ∃ α: Fin n → Set ℂ, M_I M n ≤ (succ_adjion (K_zero M) n α) ∧ succ_adjion_root (K_zero M) n α ∧ ConjClosed (succ_adjion (K_zero M) n α) := by
  induction n
  case zero =>
    refine ⟨λ _ ↦ ∅, ?_, ?_⟩
    . simp only [M_I, succ_adjion, Set.iUnion_of_empty, adjoin_empty, coe_bot, Set.le_eq_subset]
      unfold Set.range
      dsimp
      simp only [Subtype.exists, exists_prop, exists_eq_right, Set.subset_setOf]
      apply M_K_zero M
    simp only [succ_adjion_root, le_of_subsingleton, Set.iUnion_empty, Set.iUnion_of_empty,
      adjoin_empty, IsEmpty.forall_iff]
    simp only [succ_adjion, Set.iUnion_of_empty, adjoin_empty, coe_bot, true_and]
    unfold Set.range
    dsimp
    simp only [Subtype.exists, exists_prop, exists_eq_right]
    apply K_zero_conjectClosed
  case succ n Ih =>
    obtain ⟨αn, h, hr, hc⟩ := Ih
    let α1 : Fin 1 → Set ℂ := λ _ ↦ (K_root  ↑(succ_adjion (K_zero M) n αn ))
    let α : Fin (n+1) → Set ℂ := Fin.append αn α1
    have split:  succ_adjion (K_zero M) (n + 1) α  = @IntermediateField.restrictScalars ( K_zero M) ℂ _ _ _ _ _ _ _ (by unfold succ_adjion; exact Subalgebra.isScalarTower_mid (IntermediateField.adjoin (↥(K_zero M)) (⋃ i, αn i)).toSubalgebra) (IntermediateField.adjoin (succ_adjion (K_zero M) n αn) ((K_root  ↑(succ_adjion (K_zero M) n αn )))):= by
      unfold succ_adjion
      have: (⋃ i, α i) = (⋃ i, αn i) ∪ (α1 1) := by
        rw[split_union_fin]
        have : ⋃ i, α1 i = (α1 1) := by
          aesop
        rw[this]
      rw[this]
      have : α1 1 = (K_root  ↑(succ_adjion (K_zero M) n αn )) := by
        rfl
      rw[this]
      symm
      apply IntermediateField.adjoin_adjoin_left
    refine ⟨α, ?_, ?_, ?_⟩
    . unfold M_I ICL_M
      simp only [Set.le_eq_subset, Set.union_subset_iff, and_assoc, split, coe_restrictScalars]
      refine ⟨?_, ?_, ?_, ?_⟩
      . apply le_trans h (by apply K_le_K_adjion)
      . have le1: ill (M_I M n) ⊆ ill (succ_adjion (K_zero M) n αn) := by
          apply ill_mono _ _ h
        have le2: ill (succ_adjion (K_zero M) n αn) ⊆ (succ_adjion (K_zero M) n αn) := by
          intro x hx
          exact @ConjClosed.ill_L' _ hc x hx
        apply le_trans le1 (by apply le_trans le2 (by apply K_le_K_adjion))
      . have : ilc (M_I M n) ⊆ ilc (succ_adjion (K_zero M) n αn) := by
          apply ilc_mono _ _ h
        apply le_trans this ?_
        simp only [Set.le_eq_subset, Set.subset_def]
        intro z hz₁
        have : ∃ ω ∈ ↑(succ_adjion (K_zero M) n αn),∃ x : ℂ, x * x = ω ∧ z ∈ ↑(succ_adjion (K_zero M) n αn)⟮x⟯ := by
          apply @ConjClosed.ilc_L' _ hc _ _
          exact hz₁
        obtain ⟨ω, hω, x, hx, hz⟩ := this
        have : x ∈ K_root  ↑(succ_adjion (K_zero M) n αn) := by
          simp only [K_root, Set.mem_setOf_eq, hx, hω]
        have : (↥(succ_adjion (K_zero M) n αn))⟮x⟯ ≤ (adjoin (↥(succ_adjion (K_zero M) n αn)) (K_root (succ_adjion (K_zero M) n αn))) := by
          apply adjoin.mono
          simp only [Set.singleton_subset_iff, Set.mem_union, this, true_or]
        exact this hz
      . have : icc (M_I M n) ⊆ icc (succ_adjion (K_zero M) n αn) := by
          apply icc_mono _ _ h
        apply le_trans this ?_
        intro z hz₁
        have : ∃ ω ∈ ↑(succ_adjion (K_zero M) n αn),∃ x : ℂ, x * x = ω ∧ z ∈ ↑(succ_adjion (K_zero M) n αn)⟮x⟯ := by
          apply @ConjClosed.icc_L _ hc
          exact hz₁
        obtain ⟨ω, hω, x, hx, hz⟩ := this
        have : x ∈ K_root  ↑(succ_adjion (K_zero M) n αn) := by
          simp only [K_root, Set.mem_setOf_eq, hx, hω]
        have : (↥(succ_adjion (K_zero M) n αn))⟮x⟯ ≤ (adjoin (↥(succ_adjion (K_zero M) n αn)) (K_root (succ_adjion (K_zero M) n αn))) := by
          apply adjoin.mono
          simp only [Set.singleton_subset_iff, Set.mem_union, this, true_or]
        exact this hz
    . apply succ_adjion_root_split (K_zero M) n  αn hr α1
      simp only [SetOfRoots, Set.union_self, Fin.isValue, α1]
      simp only [K_root, succ_adjion, Set.mem_setOf_eq, imp_self, implies_true]
    . rw[split]
      unfold succ_adjion
      simp only [coe_restrictScalars]
      have: ConjClosed (K_root ↑(succ_adjion (K_zero M) n αn) ) := {
        equal := by
          symm
          simp [conj_set, Set.ext_iff]
          suffices  ∀ x : ℂ, x ∈ K_root  ↑(succ_adjion (K_zero M) n αn) → starRingEnd ℂ x ∈ K_root  ↑(succ_adjion (K_zero M) n αn) by
            intro x
            apply Iff.intro
            · aesop
            · intro a
              apply Exists.intro
              apply And.intro
              apply this
              exact a
              simp_all only [RingHomCompTriple.comp_apply, RingHom.id_apply]
          intro x hx
          simp_all [K_root, Set.mem_setOf_eq, ]
          rw[(RingHom.map_mul (starRingEnd ℂ) x x).symm]
          have (z : ℂ) (h: z ∈ succ_adjion (K_zero M) n αn): starRingEnd ℂ z ∈  succ_adjion (K_zero M) n αn := by
            exact @ConjClosed.conj_L _ hc z h
          exact this (x*x) hx
        }
      exact @conj_adjion' (K_zero M) (adjoin (↥(K_zero M)) (⋃ i, αn i)) hc (K_root (adjoin (↥(K_zero M)) (⋃ i, αn i))) this

lemma chain_iff_adjion_roots (M : Set ℂ) (h₀ : 0 ∈ M) (h₁ : 1 ∈ M): (∃n, ∃ α: Fin n → Set ℂ, z ∈ (succ_adjion (K_zero M) n α) ∧ succ_adjion_root (K_zero M) n α) ↔  (∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (h: ∀i,  L i ≤ L (i + 1)),
    z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2)) := by sorry

theorem Classfication_z_in_M_inf  (M : Set ℂ) (z : ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) : z ∈ M_inf M ↔ ∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (_: ∀i,  L i ≤ L (i + 1)),
    z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2) := by
  refine ⟨?_, ?_⟩
  . intro h
    rw [←chain_iff_adjion_roots M h₀ h₁]
    rw[ M_inf_in_M_I] at h
    obtain ⟨n, h ⟩ := h
    have: ∃ α,  M_I M n ≤ succ_adjion (K_zero M) n α ∧ succ_adjion_root (K_zero M) n α  ∧ ConjClosed (succ_adjion (K_zero M) n α) := by
      apply test' _ h₀ h₁
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

lemma Classfication_z_in_M_inf_2m {M : Set ℂ} (h₀: 0 ∈ M) (h₁:1 ∈ M) (z : ℂ) :
  z ∈ M_inf M →  ∃ (m : ℕ) ,((2  : ℕ) ^ m) = Polynomial.degree (minpoly (K_zero M) z)  := by sorry

lemma Classfication_z_in_M_inf_2m_not {M : Set ℂ} (h₀: 0 ∈ M) (h₁:1 ∈ M) (z : ℂ) :
  ¬ (∃ (m : ℕ) ,((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z)) → z ∉ M_inf M := by
    apply Not.imp_symm
    simp only [not_not, Nat.cast_ofNat]
    apply Classfication_z_in_M_inf_2m (h₀: 0 ∈ M) (h₁:1 ∈ M)