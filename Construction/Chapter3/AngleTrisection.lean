import Construction.Chapter2.ClasificationMinf
import Construction.NotMyCode.map_of_isScalarTower

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.RingTheory.Polynomial.RationalRoot



open Polynomial IsFractionRing
open Construction

noncomputable def H : Polynomial ℚ := X ^ 3 - (Polynomial.C (6/8) * X) - Polynomial.C (1/8)  -- x^3 - 6/8 x - 1/8
noncomputable def H' : Polynomial ℤ := Polynomial.C 8 * X ^ 3 - Polynomial.C 6 * X - 1

lemma H_degree : H.natDegree = 3 := by
  have h: H = Polynomial.C 1 * X ^ 3 + Polynomial.C 0 * X ^ 2 + Polynomial.C ((- 1) * (6/8)) * X + Polynomial.C ((- 1) * (1/8)) := by rw[H, Polynomial.C_mul (a:= -(1:ℚ)) (b:= (6/8:ℚ)), Polynomial.C_mul (a:= -(1:ℚ)) (b:= (1/8:ℚ))]; simp[Mathlib.Tactic.RingNF.add_neg]
  apply LE.le.antisymm'
  . rw[H]
    simp
    rw[Polynomial.natDegree_sub (p:= (X ^ 3)) (q:= ((Polynomial.C (6/8) * X)))]
    apply Eq.le
    simp[Polynomial.natDegree_sub_eq_right_of_natDegree_lt (p:= (Polynomial.C (6/8) * X)) (q:= (X^3 :ℚ[X])), Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
  . simp_rw[h]
    apply Polynomial.natDegree_cubic_le

--! not needed
lemma HM: Monic H := by
  refine monic_of_natDegree_le_of_coeff_eq_one ?n ?pn ?p1
  . use 3
  . apply Eq.le
    apply H_degree
  . rw[H]; simp

lemma H_H' : (Polynomial.C 8) * H = Polynomial.map (algebraMap ℤ ℚ) H' := by
  rw [H, H']
  ext n : 1
  simp only [map_ofNat, one_div, coeff_ofNat_mul, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X,
    mul_ite, mul_one, mul_zero, coeff_C, algebraMap_int_eq, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_ofNat, Polynomial.map_pow, map_X, Polynomial.map_one, coeff_one]
  split_ifs <;> norm_num

lemma H'_degree : H'.natDegree = 3 := by
  rw [H']
  compute_degree!

lemma H_monic : H.Monic := by
  unfold H
  monicity!

lemma H_ne_zero : H ≠ 0 := fun h ↦ by simpa [h] using H_degree

lemma H'_coeff_zero : H'.coeff 0 = -1 := by simp [H']

lemma H'_leading : H'.leadingCoeff = 8 := by
  rw [leadingCoeff, H'_degree, H']
  simp [coeff_one, coeff_X]

lemma H'_roots_num {a : ℚ} (ha : aeval a H' = 0) : num ℤ a ∣ -1 := by
  convert num_dvd_of_is_root ha
  exact H'_coeff_zero.symm

lemma H'_roots_den {a : ℚ} (ha : aeval a H' = 0) : (den ℤ a : ℤ) ∣ 8 := by
  convert den_dvd_of_is_root ha
  exact H'_leading.symm

lemma roots_H_H' {a : ℚ} (ha : a ∈ H.roots) : aeval a H' = 0 := by
  have : aeval a ((Polynomial.C 8) * H) = 0 := by
    rw [mem_roots H_ne_zero, IsRoot.def] at ha
    simp [ha]
  rwa [H_H', aeval_map_algebraMap] at this

lemma roots_num {a : ℚ} (ha : a ∈ H.roots) : num ℤ a = 1 ∨ num ℤ a = -1 := by
  have := H'_roots_num (roots_H_H' ha)
  rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_neg, Int.natAbs_one, Nat.dvd_one,
    Int.natAbs_eq_iff, Nat.cast_one] at this

lemma roots_den_abs {a : ℚ} (ha : a ∈ H.roots) :
    (den ℤ a : ℤ).natAbs ∈ ({1, 2, 4, 8} : Finset ℕ) := by
  rw [show {1, 2, 4, 8} = Nat.divisors 8 from rfl, Nat.mem_divisors, ← Int.natCast_dvd_natCast]
  exact ⟨by simp [H'_roots_den (roots_H_H' ha)], by norm_num⟩

lemma roots_den {a : ℚ} (ha : a ∈ H.roots) :
    (den ℤ a : ℤ) ∈ ({1, -1, 2, -2, 4, -4, 8, -8} : Finset ℤ) := by
  have := roots_den_abs ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at this --can I use `fin_cases`?
  rcases this with (h | h | h | h) <;> rcases Int.natAbs_eq_iff.1 h with (h | h) <;> simp [h]

lemma H_roots: ¬ ∃ a, a ∈ H.roots := by
  intro ⟨a, ha⟩
  have := roots_den ha
  simp only [Int.reduceNeg, Finset.mem_insert, OneMemClass.coe_eq_one, Finset.mem_singleton] at this
  have num := roots_num ha
  rw [mem_roots H_ne_zero, IsRoot.def, H, eval_sub, eval_sub, eval_pow, eval_X, eval_mul, eval_C,
    eval_X, eval_C, ← mk'_num_den' ℤ a] at ha
  simp only [algebraMap_int_eq, eq_intCast, div_pow, one_div] at ha
  rcases num with (h | h) <;>
  rcases this with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> norm_num [h, h1] at ha

lemma H_irreducible : Irreducible H := by
  rw[irreducible_iff_roots_eq_zero_of_degree_le_three]
  . exact Multiset.eq_zero_of_forall_not_mem (fun a ha ↦ H_roots ⟨a, ha⟩)
  . apply le_trans (b:=3)
    linarith
    apply Eq.le
    symm
    apply H_degree
  . apply Eq.le
    apply H_degree

section
noncomputable def H'' : Polynomial ℂ := Polynomial.C 8 * X ^ 3 - (Polynomial.C 6 * X) - Polynomial.C 1
noncomputable def α  := (Real.cos (Real.pi / 3 / 3) : ℂ)

open Complex
lemma H''_alpha_zero: 8* Complex.cos (↑Real.pi / 3 / 3) ^ 3 - 6 * Complex.cos (↑Real.pi / 3 / 3) - 1 = 0 := by
  suffices 4 * cos (Real.pi / 3 / 3) ^ 3 - 3 * cos (↑Real.pi / 3 / 3) = 1/2 by
    linear_combination 2 * this
  rw [← Complex.cos_three_mul]
  suffices cos (Real.pi / 3) = 1/2 by
    rw [← this]
    congr 1
    field_simp
    ring
  norm_cast
  rw[Real.cos_pi_div_three]
  simp

lemma H_alpha_zero: 8 * (Complex.cos (↑Real.pi / 3 / 3) ^ 3 - 6 / 8 * Complex.cos (↑Real.pi / 3 / 3) - 8⁻¹) = 0 := by
  rw[mul_sub, mul_sub, ← mul_assoc, mul_div]; simp
  convert  H''_alpha_zero


lemma exp_pi_ninth : Polynomial.degree (minpoly ℚ (Real.cos ((Real.pi/3)/3): ℂ)) = 3:= by
  have h: minpoly ℚ ((Real.cos ((Real.pi/3)/3)): ℂ) = H := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    case hp1 => exact H_irreducible
    case hp2 =>
      simp[H]; rw[←zero_div 8, eq_div_iff_mul_eq, mul_comm]
      exact H_alpha_zero; simp
    case hp3 =>
      exact HM
  rw[h, Polynomial.degree_eq_natDegree]
  norm_cast
  apply H_degree
  by_contra h'
  have h₀: Polynomial.natDegree H = 0 := by rw[h']; apply Polynomial.natDegree_zero
  have h₁: Polynomial.natDegree H = 3 := by exact H_degree
  have h₂: 0 = 3 := by rw[←h₀, h₁]
  contradiction

--! Check
lemma real_component_in_M_inf (M : Set ℂ) (h₀ : 0 ∈ M) (h₁ : 1 ∈ M):  x.re ∉ M_inf M → x ∉ M_inf M := by
  by_contra h
  simp at h
  obtain ⟨ _, h⟩ := h
  have : ↑x.re ∈ M_inf M := by
    exact real_in_M_inf M h₀ h₁ _ h
  contradiction

lemma not_mod_eq_imp_not_eq (a b n : ℕ ) (h : ¬ a % n = b % n) : ¬ a = b := by
  exact fun a_1 ↦ h (congrFun (congrArg HMod.hMod a_1) n)

--lemma dim_k_zero_ang: ∃ j:ℕ, FiniteDimensional.finrank ℚ ↥(K_zero {0, 1, Complex.exp (Complex.I * ↑Real.pi / 3)}) = (2 ^ j) := by sorry

lemma h: (K_zero ({0, 1, Complex.exp (Complex.I * ↑Real.pi / 3)} : Set ℂ)) = (IntermediateField.adjoin ℚ
    {Complex.exp (Complex.I * ↑Real.pi / 3), (starRingEnd ℂ) (Complex.exp (Complex.I * ↑Real.pi / 3))}) := by
  simp only [K_zero, conj_set, pow_one]
  have: ({0, 1, Complex.exp (Complex.I * ↑Real.pi / 3)} ∪ {x | ∃ z ∈ ({0, 1, Complex.exp (Complex.I * ↑Real.pi / 3)} : Set ℂ), (starRingEnd ℂ) z = x}) = {0, (1:ℂ)} ∪ {Complex.exp (Complex.I * ↑Real.pi / 3), (starRingEnd ℂ) (Complex.exp (Complex.I * ↑Real.pi / 3))} := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, map_zero, map_one,
      exists_eq_left, Set.union_insert, Set.union_singleton]
    ext x
    simp_all only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, or_assoc]
    rw[@eq_comm _ 0, @eq_comm _ 1, @or_comm (x = Complex.exp (Complex.I * ↑Real.pi / 3)), or_assoc,
      or_assoc, ←or_assoc, ←@or_assoc (x=0), or_self_left, or_assoc, ←or_assoc, or_comm,
      @or_comm ((starRingEnd ℂ) (Complex.exp (Complex.I * ↑Real.pi / 3)) = x), @eq_comm _ _ x, or_assoc]
  rw[this, ←IntermediateField.adjoin_adjoin_left]
  have: IntermediateField.adjoin ℚ {(0:ℂ), 1} = (⊥: IntermediateField ℚ ℂ) := le_antisymm (IntermediateField.adjoin_le_iff.mpr
    (Set.pair_subset_iff.mpr ⟨(zero_mem ⊥),(one_mem ⊥)⟩)) (by exact OrderBot.bot_le (IntermediateField.adjoin ℚ {0, 1}))
  sorry
  -- rw[this]
  -- norm_cast
  -- rw [IntermediateField.restrictScalars_adjoin]
  -- rw[←IntermediateField.adjoin_adjoin_left]

--lemma X: 1 < FiniteDimensional.finrank ℚ  (IntermediateField.adjoin ℚ {Complex.exp (Complex.I * ↑Real.pi / 3), (starRingEnd ℂ) (Complex.exp (Complex.I * ↑Real.pi / 3))}) := by sorry

example: x = 2 ↔ 1 < x ∧ x ≤ 2 := by
  rw [Nat.le_antisymm_iff, and_comm, Nat.succ_le_iff]


lemma le_adjion_root_three:  Complex.exp (Complex.I * ↑Real.pi / 3) ∈ IntermediateField.adjoin ℚ {Real.sqrt 3 * Complex.I} := by
  rw[←mul_div, mul_comm, ←Complex.cos_add_sin_I]
  norm_cast
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  rw[mul_comm, mul_div, mul_comm]
  refine add_mem (div_mem (OneMemClass.one_mem _ ) (ofNat_mem _ 2)) ?_
  exact (div_mem (IntermediateField.mem_adjoin_simple_self _ _) (ofNat_mem _ 2))

lemma le_adjion_root_three': (starRingEnd ℂ) (Complex.exp (Complex.I * ↑Real.pi / 3)) ∈ IntermediateField.adjoin ℚ {Real.sqrt 3 * Complex.I} := by
  rw[←mul_div, mul_comm, ←Complex.cos_add_sin_I]
  norm_cast
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three, map_add, conj_ofReal, map_mul, conj_ofReal,
    Complex.conj_I, mul_comm, neg_mul, Mathlib.Tactic.RingNF.add_neg]
  push_cast
  rw[mul_div, mul_comm]
  refine sub_mem (div_mem (OneMemClass.one_mem _ ) (ofNat_mem _ 2)) ?_
  exact (div_mem (IntermediateField.mem_adjoin_simple_self _ _) (ofNat_mem _ 2))


noncomputable def P : Polynomial ℚ := Polynomial.X ^ 2 +Polynomial.C 3

lemma P_degree : natDegree P = 2 := by
  simp only [natDegree_add_C, natDegree_pow, natDegree_X, mul_one, P]

lemma P_eval: (aeval (↑√3 * I)) P = 0 := by
  simp only [map_add, map_pow, aeval_X, mul_pow, I_sq, mul_neg, mul_one, aeval_C,
    eq_ratCast, Rat.cast_ofNat, P]
  norm_cast
  rw[Real.sq_sqrt]
  ring_nf
  linarith


lemma degrre_root_three: natDegree (minpoly ℚ (Real.sqrt 3 * Complex.I)) = 2 := by
  have : P = minpoly ℚ (Real.sqrt 3 * Complex.I) := by
    refine minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_
    . simp only [P]
      rw[irreducible_iff_roots_eq_zero_of_degree_le_three]
      . refine Multiset.eq_zero_of_forall_not_mem ?_
        simp only [mem_roots', ne_eq, IsRoot.def, eval_add, eval_pow, eval_X, eval_C, not_and]
        intros a _
        by_contra h
        rw[add_eq_zero_iff_eq_neg] at h
        have: 0 ≤  a ^ 2  := sq_nonneg a
        have: ¬ 0 ≤ a^2 := by
          rw[h]
          linarith
        contradiction
      . exact Nat.le_of_eq (id (Eq.symm P_degree))
      . simp only [natDegree_add_C, natDegree_pow, natDegree_X, mul_one, Nat.reduceLeDiff]
    . exact P_eval
    . refine monic_X_pow_add_C 3 (Ne.symm (Nat.zero_ne_add_one 1))
  rw[← this]
  simp only [P, natDegree_add_C, natDegree_pow, natDegree_X, mul_one]

lemma z_in_bot_Q(z : ℂ) : z ∈ (⊥ : IntermediateField ℚ ℂ) →  z.im = 0 := by
  rw [IntermediateField.mem_bot, Set.mem_range]
  intro h
  obtain ⟨x, h⟩ := h
  rw [←h]
  simp only [eq_ratCast, ratCast_im]

lemma z_in_bot_Q_not (z : ℂ):  ¬ (z.im = 0) → z ∉ (⊥ : IntermediateField ℚ ℂ) := by
  apply  Not.imp_symm
  rw [Mathlib.Tactic.PushNeg.not_not_eq]
  exact z_in_bot_Q z

lemma finrank_zero (L : IntermediateField ℚ ℂ): (¬ FiniteDimensional ℚ L) → FiniteDimensional.finrank ℚ L = 0 := by
  intro h
  exact FiniteDimensional.finrank_of_not_finite h

lemma eaual_adjion_root_three: IntermediateField.adjoin ℚ {Real.sqrt 3 * Complex.I} = IntermediateField.adjoin ℚ {cexp (I * ↑Real.pi / 3), (starRingEnd ℂ) (cexp (I * ↑Real.pi / 3))} := by
  apply le_antisymm
  . simp only [IntermediateField.adjoin_le_iff, Set.le_eq_subset, Set.singleton_subset_iff,
      SetLike.mem_coe]
    have: (1 / 2) + (√3 * I / 2) ∈ IntermediateField.adjoin ℚ {cexp (I * ↑Real.pi / 3), (starRingEnd ℂ) (cexp (I * ↑Real.pi / 3))} := by
      apply IntermediateField.subset_adjoin
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      left
      rw[←mul_div I , mul_comm I, ←Complex.cos_add_sin_I]
      norm_cast
      rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
      push_cast
      ring
    have: 2 * ((1 / 2) + (√3 * I / 2)) - 1 ∈ IntermediateField.adjoin ℚ {cexp (I * ↑Real.pi / 3), (starRingEnd ℂ) (cexp (I * ↑Real.pi / 3))} := by
      exact sub_mem (mul_mem (ofNat_mem _ 2) this) (IntermediateField.one_mem _)--(ofNat_mem _ 1)
    ring_nf at this ⊢
    exact this

  . simp only [IntermediateField.adjoin_le_iff, Set.le_eq_subset]
    rw[Set.pair_subset_iff]
    exact ⟨le_adjion_root_three, le_adjion_root_three'⟩

lemma pi_third_not_in_M_inf :
  (Complex.exp (Complex.I * (Real.pi/3)/3) : ℂ) ∉ M_inf {(0:ℂ) ,1 ,  Complex.exp (Complex.I *Real.pi/3) } := by
  apply real_component_in_M_inf _ (by simp) (by simp)
  apply Classfication_z_in_M_inf_2m_rat (Set.mem_insert 0 {1, cexp (I * ↑Real.pi / 3)})
  . simp only [Set.mem_insert_iff, one_ne_zero, Set.mem_singleton_iff, true_or, or_true]
  . rw[h]
    refine ⟨1, ?_⟩
    rw[←eaual_adjion_root_three, pow_one, ←degrre_root_three, IntermediateField.adjoin.finrank]
    . exact ⟨P, (monic_X_pow_add_C 3 (Ne.symm (Nat.zero_ne_add_one 1))), P_eval⟩
  simp
  intro x
  have h: ↑(Complex.exp (Complex.I * (↑Real.pi / 3) / 3)).re = (Real.cos ((Real.pi/3)/3): ℂ):= by
    rw[←mul_div I , mul_comm I, ←Complex.cos_add_sin_I]
    norm_cast
    simp only [ofReal_ofNat, add_re, mul_re, I_re, mul_zero,
      I_im, mul_one, zero_sub, ofReal_re, ofReal_im, neg_zero, add_zero]
  rw[h]
  have h: ¬ 2 ^ x =  Polynomial.degree (minpoly ℚ ((Real.cos ((Real.pi/3)/3)): ℂ)) := by
    rw[exp_pi_ninth]
    cases x with
      | zero => simp
      | succ x =>
        norm_cast
        rw[pow_succ]
        apply not_mod_eq_imp_not_eq (n:= 2)
        norm_num
  exact h

variable (α : ℂ)
lemma Angle_not_Trisectable :
  ∃ (α : ℂ), (Complex.exp (Complex.I * α/3) : ℂ) ∉ M_inf {(0:ℂ) ,1, Complex.exp (Complex.I * α)} := by
  use (Real.pi/3)
  nth_rw 2 [←mul_div_assoc]
  apply pi_third_not_in_M_inf

--end constructionAngleTrisection
