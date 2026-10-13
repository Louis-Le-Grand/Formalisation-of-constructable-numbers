import Construction.Chapter2.KZero
import Construction.NotMyCode.PR14987
import Construction.NotMyCode.DegreeTwo
import Construction.NotMyCode.RootTower


set_option backward.isDefEq.respectTransparency false

open IntermediateField Construction

lemma rat_mem_M_inf (M : Set ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M): ∀ x : ℚ, (algebraMap ℚ ℂ) x ∈ MField M h₀ h₁ := by
  intro x
  simp_all only [eq_ratCast]
  apply SubfieldClass.ratCast_mem

lemma adjoin_in_MField' (M : Set ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) (L : ℕ →  IntermediateField ℚ ℂ)
  (h: ∀i,  L i ≤ L (i + 1)) (hL₀: K_zero M = L 0) (n: ℕ)
  (h_deg: ∀ i < n, relfinrank (L i) (L (i+1)) = 2) : (L n).carrier ≤ MField M h₀ h₁ := by
  induction n
  case zero =>
    rw[←hL₀]
    exact K_zero_in_MField M h₀ h₁
  case succ n Ih =>
    have hLn: (L n).carrier ≤ ↑(MField M h₀ h₁) := by
      apply Ih
      intro i hi
      specialize h_deg i (by linarith)
      exact h_deg
    have : ∃ x, extendScalars (h n) = (adjoin (L n) {x}) ∧ x^2 ∈ L n:=by
      have: relfinrank (L n) (L (n + 1)) = 2 := h_deg n Nat.le.refl
      rw[relfinrank_eq_finrank_of_le (h n), dergree_two_eq_sqr] at this
      obtain ⟨x, hx2, _, h⟩ := this
      refine ⟨x, h, hx2⟩
    obtain ⟨x, hx, hx2⟩ := this
    have hx' : x ∈  (MField M h₀ h₁).toIntermediateField (rat_mem_M_inf M h₀ h₁) := by
      have: x^2 ∈ (MField M h₀ h₁).toIntermediateField (rat_mem_M_inf M h₀ h₁) := by
        exact hLn hx2
      have : x ^ 2 ∈ (MField M h₀ h₁):= by
        rw[←IntermediateField.mem_carrier] at this
        exact this
      have: ∃ y : (MField M h₀ h₁), y*y = x^2 := by
        exact MField_QuadraticClosed_def M h₀ h₁ this
      simp only [Subtype.exists, exists_prop] at this
      obtain ⟨y, hy, hyx⟩ := this
      rw [←sq, ←sub_eq_zero, pow_two_sub_pow_two, mul_eq_zero] at hyx
      cases hyx with
        | inl h => rw [add_eq_zero_iff_neg_eq] at h; rw[←h]; exact IntermediateField.neg_mem _ hy
        | inr h => rw [sub_eq_zero] at h; rw [←h]; exact hy
    have: L (n + 1) ≤ (MField M h₀ h₁).toIntermediateField (rat_mem_M_inf M h₀ h₁)  := by
      have: restrictScalars ℚ (extendScalars (h n)) ≤ (MField M h₀ h₁).toIntermediateField (rat_mem_M_inf M h₀ h₁) := by
        rw[hx]
        simp only [coe_toSubfield, restrictScalars_adjoin, adjoin_le_iff, Set.le_eq_subset,
          Set.union_subset_iff, SetLike.coe_subset_coe]
        exact ⟨hLn, Set.singleton_subset_iff.mpr hx'⟩
      exact this
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring, coe_toSubalgebra,
      Set.le_eq_subset, Set.subset_def, SetLike.mem_coe]
    intro x hx
    simp_all only [SetLike.mem_coe]
    exact this hx

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
  intro h1 i x hx
  by_cases hin : i.val < n
  · let k : Fin n := i.castLT hin
    have hx' : x ∈ α k := by
      simpa [Fin.append, Fin.addCases, hin, k] using hx
    apply (IntermediateField.adjoin.mono K _ _ ?_) (h k x hx')
    intro y hy
    obtain ⟨j, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hj, hy⟩ := Set.mem_iUnion.mp hy
    apply Set.mem_iUnion.mpr ⟨j.castSucc, ?_⟩
    apply Set.mem_iUnion.mpr ⟨?_, ?_⟩
    · exact hj
    · simpa [Fin.append, Fin.addCases] using hy
  · have hi : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    subst i
    have hx' : x ∈ α₁ 1 := by
      have happ : Fin.append α α₁ (Fin.last n) = α₁ 1 := by
        rw [show Fin.last n = Fin.natAdd n (0 : Fin 1) by ext; simp]
        rw [Fin.append_right]
        rfl
      rwa [happ] at hx
    apply (IntermediateField.adjoin.mono K _ _ ?_) (h1 x hx')
    intro y hy
    obtain ⟨j, hy⟩ := Set.mem_iUnion.mp hy
    apply Set.mem_iUnion.mpr ⟨j.castSucc, ?_⟩
    exact Set.mem_iUnion.mpr ⟨Fin.castSucc_lt_last j, by simpa [Fin.append, Fin.addCases] using hy⟩


--! Should be in Lean
lemma split_union_fin (n m: ℕ) (α₁ : Fin n → Set ℂ) (α₂ : Fin m → Set ℂ): ⋃ i, Fin.append α₁ α₂ i = (⋃ i, α₁ i) ∪ ⋃ i, α₂ i := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : i.val < n
    · left
      exact ⟨i.castLT h, by simpa [Fin.append, Fin.addCases, h] using hi⟩
    · right
      refine ⟨Fin.subNat n (Fin.cast (Nat.add_comm n m) i) (by simpa using Nat.le_of_not_gt h), ?_⟩
      simpa [Fin.append, Fin.addCases, h] using hi
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨Fin.castAdd m i, by simpa only [Fin.append_left] using hi⟩
    · exact ⟨Fin.natAdd n i, by simpa only [Fin.append_right] using hi⟩

def K_root (K : IntermediateField E F): Set F := {x : F | x * x ∈ K}

end test

lemma M_i_in_K_i (M : Set ℂ) (_: 0 ∈ M) (_:1 ∈ M) (n : ℕ) : ∃ α: Fin n → Set ℂ, M_I M n ≤ (succ_adjion (K_zero M) n α) ∧ succ_adjion_root (K_zero M) n α ∧ ConjClosed (succ_adjion (K_zero M) n α) := by
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

namespace QuadraticChain

lemma Tower.exists_layers {K P : QuadraticChain.Field} (h : Tower K P) :
    ∃ (n : ℕ) (α : Fin n → Set ℂ),
      P = (succ_adjion K n α).restrictScalars ℚ ∧ succ_adjion_root K n α := by
  induction h with
  | base =>
    refine ⟨0, Fin.elim0, ?_, ?_⟩
    · simp [succ_adjion]
    · intro i
      exact Fin.elim0 i
  | @step P _ x hx ih =>
    obtain ⟨n, α, he, hr⟩ := ih
    let β : Fin 1 → Set ℂ := fun _ => {x}
    have hb : (⋃ i, β i) = {x} := by simp [β]
    refine ⟨n + 1, Fin.append α β, ?_, ?_⟩
    · rw [he]
      simp only [succ_adjion, split_union_fin, hb, restrict_adjoin,
        QuadraticChain.adjoin_union, sup_assoc]
    · apply succ_adjion_root_split K n α hr β
      intro a ha
      have ha' : a = x := Set.mem_singleton_iff.mp ha
      subst a
      have hx' : x ^ 2 ∈ succ_adjion K n α := by
        rw [he] at hx
        exact hx
      simpa only [sq, succ_adjion] using hx'

lemma layers_le_closure (K : QuadraticChain.Field) (n : ℕ) (α : Fin n → Set ℂ)
    (hr : succ_adjion_root K n α) :
    (succ_adjion K n α).restrictScalars ℚ ≤ QuadraticChain.closure K := by
  have hα : ∀ i, α i ⊆ QuadraticChain.closure K := by
    intro i
    induction i using WellFoundedLT.induction
    rename_i j ih
    intro x hx
    apply root_mem_closure
    have hp : (adjoin K (⋃ k : Fin n, ⋃ (_ : k < j), α k)).restrictScalars ℚ ≤
        QuadraticChain.closure K := by
      rw [restrict_adjoin]
      refine sup_le (le_closure K) (adjoin_le_iff.mpr ?_)
      intro y hy
      obtain ⟨k, hy⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hk, hy⟩ := Set.mem_iUnion.mp hy
      exact ih k hk hy
    exact hp (by simpa only [sq, mem_restrictScalars] using hr j x hx)
  rw [succ_adjion, restrict_adjoin]
  exact sup_le (le_closure K) (adjoin_le_iff.mpr (Set.iUnion_subset hα))

end QuadraticChain

lemma chain_iff_adjion_roots (M : Set ℂ) (h₀ : 0 ∈ M) (h₁ : 1 ∈ M): (∃n, ∃ α: Fin n → Set ℂ, z ∈ (succ_adjion (K_zero M) n α) ∧ succ_adjion_root (K_zero M) n α) ↔  (∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (h: ∀i,  L i ≤ L (i + 1)),
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
open Module
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
    subst a
    simpa using h
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


lemma mulfinrank_help (R K L: IntermediateField ℚ ℂ) (h₁: R ≤ K) (h₂: K ≤ L) : Module.finrank R (extendScalars h₁) *
    Module.finrank K (extendScalars h₂) = Module.finrank R (extendScalars (Trans.trans h₁ h₂)) := by
  rw [←IntermediateField.relfinrank_eq_finrank_of_le h₁,
  ←IntermediateField.relfinrank_eq_finrank_of_le (Trans.trans h₁ h₂),
  ←IntermediateField.relfinrank_mul_relfinrank h₁ h₂]
  have: Module.finrank K (extendScalars h₂) = K.relfinrank L := by
    exact Eq.symm (relfinrank_eq_finrank_of_le h₂)
  simp only [mul_eq_mul_left_iff, this]

lemma degree_of_Ln (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (h:  ∃   (_: ∀i,  L i ≤ L (i + 1)),
    K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2)): relfinrank (K_zero M) (L n) = 2^n := by
  obtain ⟨hL, hL0, h_degree⟩ := h
  have hmono : Monotone L := monotone_nat_of_le_succ hL
  induction n with
  | zero => simp only [hL0, relfinrank_self, pow_zero]
  | succ n ih =>
    have hn : K_zero M ≤ L n := hL0.symm ▸ hmono (Nat.zero_le n)
    rw [← relfinrank_mul_relfinrank hn (hL n),
      ih (fun i hi => h_degree i (by omega)), h_degree n (by omega), pow_succ]


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
  have hm: ∃m, Module.finrank (K_zero M) ((K_zero M) ⟮z⟯) = 2^m := by
    have : Module.finrank (K_zero M) ((K_zero M) ⟮z⟯) ∣ 2^n := by
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


lemma Classfication_z_in_M_inf_2m_rat {M : Set ℂ} (h₀: 0 ∈ M) (h₁:1 ∈ M) (z : ℂ) (h: ∃j:ℕ, Module.finrank ℚ (K_zero M) = 2^j) :
    ¬ (∃ m, 2 ^ m = (minpoly ℚ z).degree) → z ∉ M_inf M := by
  apply Not.imp_symm
  simp only [not_not, Nat.cast_ofNat]
  have:  (∃ m ,2 ^ m = (minpoly (K_zero M) z).degree) → ∃ m, 2 ^ m = (minpoly ℚ z).degree := by
    intro h'
    obtain ⟨m, hm⟩ := h'
    obtain ⟨j, hj⟩ := h
    letI : IsScalarTower ℚ (K_zero M) ((K_zero M)⟮z⟯) :=
      IsScalarTower.of_algebraMap_eq' rfl
    have hmj: Module.finrank ℚ (restrictScalars ℚ ((K_zero M) ⟮z⟯)) = 2^(m+j) := by
      have: minpoly (↥(K_zero M)) z ≠ 0 := by
        apply Polynomial.zero_le_degree_iff.mp
        rw[←hm]
        simp only [Nat.ofNat_nonneg, pow_nonneg]
      rw[Polynomial.degree_eq_natDegree this] at hm
      norm_cast at hm
      rw[pow_add, ←hj, hm,  ← IntermediateField.adjoin.finrank, mul_comm]
      symm
      apply Module.finrank_mul_finrank
      . by_contra h
        have: minpoly (↥(K_zero M)) z = 0:= minpoly.eq_zero h
        contradiction
    have hdiv: Module.finrank ℚ ℚ⟮z⟯ ∣ Module.finrank ℚ (restrictScalars ℚ ((K_zero M) ⟮z⟯)) := by
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
