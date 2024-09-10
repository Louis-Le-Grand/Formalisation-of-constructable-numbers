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


lemma pi_third_not_in_M_inf :
  (Complex.exp (Complex.I * (Real.pi/3)/3) : ℂ) ∉ M_inf {(0:ℂ) ,1 ,  Complex.exp (Complex.I *Real.pi/3) } := by
  apply real_component_in_M_inf _ (by simp) (by simp)
  apply Classfication_z_in_M_inf_2m_rat (Set.mem_insert 0 {1, cexp (I * ↑Real.pi / 3)})
  . simp only [Set.mem_insert_iff, one_ne_zero, Set.mem_singleton_iff, true_or, or_true]
  . sorry --exact dim_k_zero_ang
  simp
  intro x
  have h: ↑(Complex.exp (Complex.I * (↑Real.pi / 3) / 3)).re = (Real.cos ((Real.pi/3)/3): ℂ):= by sorry
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
