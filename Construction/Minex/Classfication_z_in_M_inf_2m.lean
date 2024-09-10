import Construction.Chapter2.KZero
import Construction.NotMyCode.PR14987
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.Nat.Factors

section pre
open IntermediateField Construction

theorem Classfication_z_in_M_inf  (M : Set ℂ) (z : ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) : z ∈ M_inf M ↔ ∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (_: ∀i,  L i ≤ L (i + 1)),
    z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2) := by sorry

end pre

open IntermediateField Construction

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

lemma Classfication_z_in_M_inf_2m {M : Set ℂ} (h₀: 0 ∈ M) (h₁:1 ∈ M) (z : ℂ) :
  z ∈ M_inf M →  ∃ (m : ℕ) ,((2  : ℕ) ^ m) = Polynomial.degree (minpoly (K_zero M) z)  := by
  intro h
  rw[Classfication_z_in_M_inf M z h₀ h₁] at h
  obtain ⟨n, L, hL, hLn, hL0, h_degree⟩ := h
  have: K_zero M ≤ L n := by
    rw[hL0]
    exact monotone_nat_of_le_succ (fun n ↦ hL n) (Nat.zero_le n)
  have hn: relfinrank (K_zero M) (L n) = 2^n := by
    induction n
    case zero => simp only [hL0, relfinrank_self, pow_zero]
    case succ n Ih =>
      rw[relfinrank_eq_finrank_of_le this]
      have hn: K_zero M ≤ L n := by
        rw[hL0]
        exact monotone_nat_of_le_succ (fun n ↦ hL n) (Nat.zero_le n)
      specialize h_degree n (by linarith)
      specialize hL n
      --rw[pow_succ, ←Ih, relfinrank_eq_finrank_of_le hn, ←h_degree, relfinrank_eq_finrank_of_le hL]
      --rw [FiniteDimensional.finrank_mul_finrank]
      sorry
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


section
variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
variable {L : IntermediateField F E}

example: FiniteDimensional.finrank F L * FiniteDimensional.finrank L E = FiniteDimensional.finrank F E := by
  rw [FiniteDimensional.finrank_mul_finrank]
end


-- lemma div_two_2pown (a n : ℕ) (h: a ∣ 2^ n) :  ∃ m : ℕ, 2 ^ m = a:= by
--   induction n
--   case zero =>
--     rw[pow_zero] at h
--     have: a = 1 := by
--       apply Nat.eq_one_of_dvd_one
--       exact h
--     rw[this]
--     exact ⟨0, rfl⟩
--   case succ n Ih =>
--     by_cases h': a ∣ 2^n
--     . exact Ih h'
--     . have h': a =  2 ^ (n+1) := by
--         by_contra h''
--         have: 2 ^ n ∣ 2 ^ (n+1) := by
--           rw[pow_succ]
--           exact dvd_mul_right _ _

--         sorry
--       rw[h']
--       exact ⟨n+1, rfl⟩

-- lemma div_two_2pown'' (a n : ℕ) (h: a ∣ 2^ n) :  ∃ m : ℕ, 2 ^ m = a:= by
--   obtain h' := Nat.eq_two_pow_or_exists_odd_prime_and_dvd a
--   have: ¬ (∃ p, Nat.Prime p ∧ p ∣ a ∧ Odd p) := by
--     by_contra h'
--     obtain ⟨p, hp, hpa, hpodd⟩ := h'
--     have: ¬ p ∣ 2^ n := by
--       by_contra h'

--       sorry
--     have: p ∣ 2^ n := Nat.dvd_trans hpa h
--     contradiction
--   simp [this] at h'
--   obtain ⟨m, hm⟩ := h'
--   exact ⟨m, Eq.symm hm⟩
