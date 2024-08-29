import Construction.Chapter2.MField
import Construction.NotMyCode.PR14987

import Mathlib.RingTheory.Norm.Basic
import Mathlib.Deprecated.Subfield


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

variable {F: Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

lemma K_le_K_adjion (K : IntermediateField F E) (M : Set E) ( x : E) (hx: x ∈ K) : x ∈ IntermediateField.adjoin K M := by
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

    -- apply conj_adjion

-- lemma conj_adjion' (K : IntermediateField ℚ ℂ) (M : Set ℂ) : ConjClosed K ∧ ConjClosed M → ConjClosed (IntermediateField.adjoin K M) := by
--   intro h
--   obtain ⟨h, hn⟩ := h
--   apply conj_adjion

--#eval (↑ℚ :IntermediateField ℚ ℂ)

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

-- noncomputable instance MField_intfield (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M) : (IntermediateField ℚ ℂ) (MField M h₀ h₁) := by
--   sorry

/- lemma M_K_zero (M : Set ℂ) (h₀: 0 ∈ M)(h₁:1 ∈ M) :  M ≤ K_zero M := by
  simp only [Set.le_eq_subset]
  sorry -/

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


-- lemma adjoin_in_MField (L : IntermediateField ℚ ℂ) (M : Set ℂ) (h₀: 0 ∈ M)(h₁:1 ∈ M) (h: K_zero M ≤ L) (h_deg: ∃ n : ℕ, IntermediateField.relfinrank (K_zero M) L = 2^n) : L.carrier ≤ MField M h₀ h₁ := by
--   obtain ⟨ n, h_deg⟩ := h_deg
--   induction n
--   case zero =>
--     have : L = K_zero M := by
--       sorry
--     rw[this]
--     exact K_zero_in_MField M h₀ h₁
--   case succ n Ih =>
--     have : ∃ L' : IntermediateField ℚ ℂ, ∃ x: ℂ, x ∈ L' ∧ L' ≤ L ∧ IntermediateField.extendScalars (F:= L') (E:= L) (by sorry) = IntermediateField.adjoin L' {x} ∧ IntermediateField.relfinrank (K_zero M) L' = 2 ^ n  := by
--       sorry
--     obtain ⟨L', hx, hL', hL, h_deg'⟩ := this
--     sorry

-- lemma  adjoin_in_MInf (L : IntermediateField ℚ ℂ) (M : Set ℂ) (h₀: 0 ∈ M)(h₁:1 ∈ M) (h: K_zero M ≤ L) (h_deg: ∃ n : ℕ, IntermediateField.relfinrank (K_zero M) L = 2^n) : L.carrier ≤ M_inf M := by
--   apply adjoin_in_MField' L M h₀ h₁ h h_deg


open IntermediateField

lemma adjoin_in_MField' (M : Set ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) (L : ℕ →  IntermediateField ℚ ℂ) (h: ∀i,  L i ≤ L (i + 1)) (hL₀: K_zero M = L 0) (n: ℕ) (h_deg: ∀ i < n, relfinrank (L i) (L (i+1)) = 2) : (L n).carrier ≤ MField M h₀ h₁ := by
  induction n
  case zero =>
    rw[←hL₀]
    exact K_zero_in_MField M h₀ h₁
  case succ n Ih =>
    have : ∃ x, IntermediateField.extendScalars (F:= L n) (E:= L (n+1)) (by apply h) = IntermediateField.adjoin (L n) {x} := by
      sorry -- use degrre of L (n+1) L n equals two and Char L i = 0
    obtain ⟨x, hx⟩ := this
    have : x^2 ∈ (L n) := by
      sorry --follows from the above
    have : x ∈ MField M h₀ h₁ := by
      have: x^2 ∈ MField M h₀ h₁ := by
        rw[←IntermediateField.mem_carrier] at this
        specialize h_deg (n) (by linarith)
        simp [h_deg]  at Ih

        sorry

      sorry -- use Quadtrtic closed and x^2 in L n, thefore in MFiled
    have : IntermediateField.extendScalars (F:= L n) (E:= L (n+1)) (by apply h) ≤ @Subfield.toIntermediateField (L n) ℂ _ _ _ (MField M h₀ h₁) (by sorry) := by -- replase soorry with Ih
      rw[hx]
      apply IntermediateField.adjoin_le_iff.mpr
      simp only [Set.le_eq_subset, Set.singleton_subset_iff, SetLike.mem_coe]
      exact this
    apply this


--! Find out if this is realy need or already in mathlib
-- open IntermediateField
-- variable (K : IntermediateField F E) (L : IntermediateField K E) [IsSeparable K E]


-- theorem dergree_two_eq_sqr :  FiniteDimensional.finrank K L = 2 ↔ ∃ x : E, x ^ 2 ∈ K ∧ ¬(x ∈ K) ∧ L = IntermediateField.adjoin K {x} := by
--   refine Iff.intro ?_ ?_
--   intros h

--   sorry
--   intros h
--   obtain ⟨x, hx, hx', hlk⟩ := h
--   rw[hlk]
--   rw[IntermediateField.adjoin.finrank]
--   have : ∃ z : K, z = x ^ 2 := by
--     simp only [Subtype.exists, exists_prop, exists_eq_right, hx]
--   obtain ⟨z, hz⟩ := this
--   let p := Polynomial.X ^ 2 - Polynomial.C z
--   have : minpoly (↥K) x = p := by
--     refine (minpoly.eq_of_irreducible_of_monic ?hp1 ?hp2 ?hp3).symm
--     . sorry
--     . simp only [map_sub,
--         map_pow,
--         Polynomial.aeval_X,
--         Polynomial.aeval_C,
--         IntermediateField.algebraMap_apply,
--         sub_self,
--         p, hz]
--     . refine Polynomial.monic_X_pow_sub_C z ?hp3.h
--       simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
--   rw[this]
--   exact Polynomial.natDegree_X_pow_sub_C
--   sorry

variable (K L : IntermediateField F E)

-- theorem Classfication_z_in_M_inf (M : Set ℂ) (z : ℂ) : z ∈ M_inf M ↔ ∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (h: ∀i,  L i ≤ L (i + 1)),
--   z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, ∃ x ∈  L (i+1),  (L i) ⟮x⟯  = IntermediateField.extendScalars (F:= (L i)) (E := (L (i + 1))) (by apply h) ∧ x ^ 2 ∈ (L i)) := by
--   sorry


-- --! Use chain only until n defined
-- -- theorem Classfication_z_in_M_inf'  (M : Set ℂ) (z : ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) : z ∈ M_inf M ↔ ∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (h: ∀i,  L i ≤ L (i + 1)),
-- --   z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2) := by

-- lemma Classfication_z_in_M_eq (M : Set ℂ) (z : ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) :
--   ∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (h: ∀i,  L i ≤ L (i + 1)),
--   z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, ∃ x ∈  L (i+1),  (L i) ⟮x⟯  = IntermediateField.extendScalars (F:= (L i)) (E := (L (i + 1))) (by apply h) ∧ x ^ 2 ∈ (L i))
--   ↔ ∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (h: ∀i,  L i ≤ L (i + 1)),
--   z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, ∃ x ∈  L (i+1),  (L i) ⟮x⟯  = IntermediateField.extendScalars (F:= (L i)) (E := (L (i + 1))) (by apply h) ∧ x ^ 2 ∈ (L i)) := by
--   sorry

-- theorem Classfication_z_in_M_inf'  (M : Set ℂ) (z : ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) : z ∈ M_inf M ↔ ∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (h: ∀i,  L i ≤ L (i + 1)),
--     z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2) := by
--   refine  ⟨?_ , ?_ ⟩
--   intro h
--   unfold M_inf at h
--   simp at h
--   obtain ⟨i, h⟩  := h
--   induction i
--   -- try to use a chain of complesx nummber, with squar in the previos field and gernerate the nesxt field
--   --generlise to use Indutcion closed field
--   sorry
--   sorry
--   intro h
--   obtain ⟨n, L, h, hz, hL₀, h_deg⟩ := h
--   have hLn: (L n).carrier ≤ MField M h₀ h₁ := by
--     apply adjoin_in_MField' M h₀ h₁ L h hL₀ n h_deg
--   simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring, coe_toSubalgebra,
--     Set.le_eq_subset, Set.subset_def, SetLike.mem_coe] at hLn
--   simp_rw[ ←Subfield.mem_carrier] at hLn
--   have : (MField M h₀ h₁).carrier = M_inf M := rfl
--   rw[this] at hLn
--   simp[hLn, hz]

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

-- lemma succ_adjion_le' (K: IntermediateField E F) (n m: ℕ) (αn: Fin n  → Set F) (αm: Fin m → Set F) : succ_adjion K m αm ≤ succ_adjion K (n+m) (Fin.append αn αm) := by
--   sorry

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
    -- --(j: Fin (n+1)) (hj: j < Fin.castLE hin (Fin.last ↑i))
    -- have : ∀ j < Fin.castLE hin (Fin.last ↑i), (Fin.append α α₁ j) = α (Fin.castLE (sorry) ( ↑j))  := by
    --   --simp only [Fin.append, Fin.addCases, Nat.lt_trans hj hin, ↓reduceDIte, Fin.castLE, Nat.succ_eq_add_one, Fin.last, Fin.val_natCast]
    --   sorry --rfl
    -- push_cast at this
    -- rw[←this] at h
    -- --exact h
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
      -- have: @Fin.subNat 1 n (@Fin.cast (n + 1) (1 + n) (Nat.add_comm n 1) (Fin.last n )) = 1  := by
      --   sorry
      -- rw[this]
      -- norm_cast
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


-- lemma succ_adjion_root_split'  (K: IntermediateField E F) (n m : ℕ) (αn: Fin n → Set F) (hn : succ_adjion_root K n αn) (αm: Fin m → Set F) (hm : succ_adjion_root K m αm) : SetOfRoots (IntermediateField.adjoin K (⋃  i, αn i)) (αm (0: Fin n)) →  succ_adjion_root K (n+m) (Fin.append αn αm) := by
--   sorry

--def M_root (M : Set ℂ) (n: ℕ) (K:IntermediateField ℚ ℂ) [ConjClosed K] (h: M_I M n ≤ K) : Set ℂ :=


--! Move to a better place
lemma L_mono (M N : Set ℂ) (h: M ⊆ N) : Construction.L M ⊆ Construction.L N := by
  unfold Construction.L
  simp only [Set.iUnion_subset_iff, Set.subset_def]
  intro l hl
  obtain ⟨z₁, z₂, hl, hz₁, hz₂, hne⟩ := hl
  refine ⟨z₁, z₂, hl,  h hz₁, h hz₂, hne⟩

lemma C_mono (M N : Set ℂ) (h: M ⊆ N) : Construction.C M ⊆ Construction.C N := by
  unfold Construction.C
  simp only [Set.iUnion_subset_iff, Set.subset_def]
  intro c hc
  obtain ⟨z, r₁, r₂, hl, hz, hr₁, hr₂⟩ := hc
  refine ⟨z, r₁, r₂, hl,  h hz, h hr₁, h hr₂⟩

lemma ill_mono (M N : Set ℂ) (h: M ⊆ N) : ill M ⊆ ill N := by
  unfold ill
  simp only [Set.iUnion_subset_iff, Set.subset_def]
  intro x hx
  obtain ⟨l₁, hl₁, l₂, hl₂, hx, hlne⟩ := hx
  refine ⟨l₁, ?_, l₂, ?_, hx, hlne⟩
  apply L_mono M N h hl₁
  apply L_mono M N h hl₂

lemma ilc_mono (M N : Set ℂ) (h: M ⊆ N) : ilc M ⊆ ilc N := by
  unfold ilc
  simp only [Set.iUnion_subset_iff, Set.subset_def]
  intro x hx
  obtain ⟨c, hc, l, hl, hx, hlne⟩ := hx
  refine ⟨c, ?_, l, ?_, hx, hlne⟩
  apply C_mono M N h hc
  apply L_mono M N h hl

lemma icc_mono (M N : Set ℂ) (h: M ⊆ N) : icc M ⊆ icc N := by
  unfold icc
  simp only [Set.iUnion_subset_iff, Set.subset_def]
  intro x hx
  obtain ⟨c₁, hc₁, c₂, hc₂, hx, hlne⟩ := hx
  refine ⟨c₁, ?_, c₂, ?_, hx, hlne⟩
  apply C_mono M N h hc₁
  apply C_mono M N h hc₂
--! Move to here

def K_root (K : IntermediateField E F): Set F := {x : F | x * x ∈ K}

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

-- lemma test (M : Set ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) (n : ℕ) : ∃ α: Fin n → Set ℂ, M_I M n ≤ (succ_adjion (K_zero M) n α) ∧ succ_adjion_root (K_zero M) n α ∧ ConjClosed (succ_adjion (K_zero M) n α) := by
--   induction n
--   case zero =>
--     refine ⟨λ i ↦ ∅, ?_, ?_⟩
--     . simp only [M_I, succ_adjion, Set.iUnion_of_empty, adjoin_empty, coe_bot, Set.le_eq_subset]
--       unfold Set.range
--       dsimp
--       simp only [Subtype.exists, exists_prop, exists_eq_right, Set.subset_setOf]
--       apply M_K_zero M
--     simp only [succ_adjion_root, le_of_subsingleton, Set.iUnion_empty, Set.iUnion_of_empty,
--       adjoin_empty, IsEmpty.forall_iff]
--     simp only [succ_adjion, Set.iUnion_of_empty, adjoin_empty, coe_bot, true_and]
--     unfold Set.range
--     dsimp
--     simp only [Subtype.exists, exists_prop, exists_eq_right]
--     apply K_zero_conjectClosed
--   case succ n Ih =>
--     obtain ⟨αn, h, hr, hc⟩ := Ih
--     let α1 : Fin 1 → Set ℂ := λ i ↦ (K_root  ↑(succ_adjion (K_zero M) n αn )) ∪ conj_set (K_root  ↑(succ_adjion (K_zero M) n αn ))
--     let α : Fin (n+1) → Set ℂ := Fin.append αn α1
--     have split:  succ_adjion (K_zero M) (n + 1) α  = @IntermediateField.restrictScalars ( K_zero M) ℂ _ _ _ _ _ _ _ (by unfold succ_adjion; exact Subalgebra.isScalarTower_mid (IntermediateField.adjoin (↥(K_zero M)) (⋃ i, αn i)).toSubalgebra) (IntermediateField.adjoin (succ_adjion (K_zero M) n αn) ((K_root  ↑(succ_adjion (K_zero M) n αn )) ∪ conj_set (K_root  ↑(succ_adjion (K_zero M) n αn )))):= by
--       -- IntermediateField.adjoin_adjoin_left
--       sorry
--     refine ⟨α, ?_, ?_, ?_⟩
--     . unfold M_I ICL_M
--       simp only [Set.le_eq_subset, Set.union_subset_iff, and_assoc, split, coe_restrictScalars]
--       refine ⟨?_, ?_, ?_, ?_⟩
--       . apply le_trans h (by apply K_le_K_adjion)
--       . have le1: ill (M_I M n) ⊆ ill (succ_adjion (K_zero M) n αn) := by
--           apply ill_mono _ _ h
--         have le2: ill (succ_adjion (K_zero M) n αn) ⊆ (succ_adjion (K_zero M) n αn) := by
--           apply ConjClosed.ill_L
--         apply le_trans le1 (by apply le_trans le2 (by apply K_le_K_adjion))
--       . have : ilc (M_I M n) ⊆ ilc (succ_adjion (K_zero M) n αn) := by
--           apply ilc_mono _ _ h
--         apply le_trans this ?_
--         simp only [Set.le_eq_subset, Set.subset_def]
--         intro z hz₁
--         have : ∃ ω ∈ ↑(succ_adjion (K_zero M) n αn),∃ x : ℂ, x * x = ω ∧ z ∈ ↑(succ_adjion (K_zero M) n αn)⟮x⟯ := by
--           apply @ConjClosed.ilc_L _ hc _ _
--           exact hz₁
--         obtain ⟨ω, hω, x, hx, hz⟩ := this
--         have : x ∈ K_root  ↑(succ_adjion (K_zero M) n αn) := by
--           simp only [K_root, Set.mem_setOf_eq, hx, hω]
--         have : (↥(succ_adjion (K_zero M) n αn))⟮x⟯ ≤ (adjoin (↥(succ_adjion (K_zero M) n αn)) (K_root (succ_adjion (K_zero M) n αn) ∪ conj_set (K_root (succ_adjion (K_zero M) n αn)))) := by
--           apply adjoin.mono
--           simp only [Set.singleton_subset_iff, Set.mem_union, this, true_or]
--         exact this hz
--       . have : icc (M_I M n) ⊆ icc (succ_adjion (K_zero M) n αn) := by
--           apply icc_mono _ _ h
--         apply le_trans this ?_
--         intro z hz₁
--         have : ∃ ω ∈ ↑(succ_adjion (K_zero M) n αn),∃ x : ℂ, x * x = ω ∧ z ∈ ↑(succ_adjion (K_zero M) n αn)⟮x⟯ := by
--           apply ConjClosed.icc_L
--           exact hz₁
--         obtain ⟨ω, hω, x, hx, hz⟩ := this
--         have : x ∈ K_root  ↑(succ_adjion (K_zero M) n αn) := by
--           simp only [K_root, Set.mem_setOf_eq, hx, hω]
--         have : (↥(succ_adjion (K_zero M) n αn))⟮x⟯ ≤ (adjoin (↥(succ_adjion (K_zero M) n αn)) (K_root (succ_adjion (K_zero M) n αn) ∪ conj_set (K_root (succ_adjion (K_zero M) n αn)))) := by
--           apply adjoin.mono
--           simp only [Set.singleton_subset_iff, Set.mem_union, this, true_or]
--         exact this hz
--     . apply succ_adjion_root_split (K_zero M) n  αn hr α1
--       have : conj_set (K_root  ↑(succ_adjion (K_zero M) n αn)) = K_root  ↑(succ_adjion (K_zero M) n αn) := by
--         simp [conj_set, Set.ext_iff]
--         suffices  ∀ x : ℂ, x ∈ K_root  ↑(succ_adjion (K_zero M) n αn) → starRingEnd ℂ x ∈ K_root  ↑(succ_adjion (K_zero M) n αn) by
--           intro x
--           apply Iff.intro
--           · intro a
--             unhygienic
--               with_reducible
--                 aesop_destruct_products
--             aesop_subst right
--             simp_all only
--           · intro a
--             apply Exists.intro
--             apply And.intro
--             apply this
--             exact a
--             simp_all only [RingHomCompTriple.comp_apply, RingHom.id_apply]
--         intro x hx
--         simp_all [K_root, Set.mem_setOf_eq, ]
--         rw[(RingHom.map_mul (starRingEnd ℂ) x x).symm]
--         have (z : ℂ) (h: z ∈ succ_adjion (K_zero M) n αn): starRingEnd ℂ z ∈  succ_adjion (K_zero M) n αn := by
--           exact @ConjClosed.conj_L _ hc z h
--         exact this (x*x) hx
--       simp only [SetOfRoots, this, Set.union_self, Fin.isValue, α1]
--       simp only [K_root, succ_adjion, Set.mem_setOf_eq, imp_self, implies_true]
--     . rw[split]
--       unfold succ_adjion
--       simp only [coe_restrictScalars]
--       have: ConjClosed (K_root (adjoin (↥(K_zero M)) (⋃ i, αn i)) ∪ conj_set (K_root (adjoin (↥(K_zero M)) (⋃ i, αn i)))) := by
--         apply ConjClosed.M_con_M
--       exact @conj_adjion' (K_zero M) (adjoin (↥(K_zero M)) (⋃ i, αn i)) hc (K_root (adjoin (↥(K_zero M)) (⋃ i, αn i)) ∪ conj_set (K_root (adjoin (↥(K_zero M)) (⋃ i, αn i)))) this

end test

open IntermediateField

variable {E : Type*} [Field E] {F : Type*} [Field F] [Algebra E F]

example (M N : Set F) (h: M ⊆ N ) : adjoin E M ≤ adjoin E N := by
  exact adjoin.mono E M N h

example (M N : Set F) (h: M ⊆ N ) (g: x∈ M): x ∈  N := by
  exact h g

example (x: ℂ ) :(starRingEnd ℂ) x * (starRingEnd ℂ) x = (starRingEnd ℂ) (x * x ) := by
  rw[(RingHom.map_mul (starRingEnd ℂ) x x).symm]

-- example: {x:ℂ|∃q:ℚ, ↑q = x} = ℚ := by
--   ext x
