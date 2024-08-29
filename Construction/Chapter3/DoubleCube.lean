import Construction.Chapter2.ClasificationMinf
import Construction.NotMyCode.map_of_isScalarTower

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.RingTheory.Polynomial.RationalRoot

open Polynomial
open Construction
noncomputable def P : (Polynomial ℚ) := X ^ 3 - Polynomial.C 2 -- x^3 - 2

lemma P_monic: Monic P := by
  refine monic_of_natDegree_le_of_coeff_eq_one ?n ?pn ?p1
  . use 3
  . apply Eq.le
    apply Polynomial.natDegree_X_pow_sub_C
  . rw[P]
    simp

theorem Z.le_of_succ_le_succ {n m : Int}: LE.le (Int.succ n) (Int.succ m) → LE.le n m := by
  unfold Int.succ
  simp

theorem Z.le_of_lt_succ {m n : Int}: LT.lt m (Int.succ n) → LE.le m n := by
  apply Z.le_of_succ_le_succ

lemma irrational_thirdroot_two: Irrational (2 ^ (1/3:ℝ)) := by
  apply irrational_nrt_of_notint_nrt 3 2
  . simp
    apply Real.rpow_inv_natCast_pow (n:= 3) (x := 2)
    . norm_num
    . simp
  . simp
    intro X
    by_contra h'
    have h'': 2 ^ (1/3:ℝ) < (2:ℝ)  := by
      nth_rewrite 2[←Real.rpow_one 2]
      rw[Real.rpow_lt_rpow_left_iff (x:=2) (y:=(1/3:ℝ)) (z:=(1:ℝ)) (by exact one_lt_two)]
      norm_num
    have h''': (1:ℝ)  < 2 ^ (1/3:ℝ)  := by
      rw[Real.one_lt_rpow_iff (x:=2) (y:=1/3)]
      norm_num
      norm_num
    norm_num at h'
    rw[h'] at h'''
    rw[h'] at h''
    have : (0:ℝ)  < X := by
      apply lt_trans (b:= (1:ℝ) )
      norm_num
      exact h'''
    simp at this
    have g : X ≤ (1:ℕ)  := by
      apply Z.le_of_lt_succ
      simp
      unfold Int.succ
      rw[one_add_one_eq_two]
      norm_cast at h''
    have g' : (1:ℕ)  < X := by norm_cast at h'''
    apply not_lt_of_le g g'
  simp

lemma if_cube_eq_two_irrat(x:ℝ): x ^ 3 = 2 → Irrational x := by
  intro h
  have h₁: 0 ≤ x := by
    rw[←Odd.pow_nonneg_iff (n:=3)]
    rw [h]
    norm_num
    rw[Nat.odd_iff]
  have h₂: x = 2 ^ (3⁻¹:ℝ):= by
    symm; rw[Real.rpow_inv_eq]
    rw[←h]
    norm_cast
    norm_num
    exact h₁
    norm_num
  rw[h₂]
  rw[inv_eq_one_div]
  convert irrational_thirdroot_two

lemma P_roots: roots P = 0 := by
  refine Multiset.eq_zero_of_forall_not_mem ?_
  simp[P]
  intro a _
  by_contra h
  have h': (a:ℝ)^3 = 2 := by
    rw[sub_eq_zero] at h
    norm_cast
  apply if_cube_eq_two_irrat a h'
  simp

lemma P_irreducible : Irreducible P := by
  rw[irreducible_iff_roots_eq_zero_of_degree_le_three]
  . exact P_roots
  . apply le_trans (b:=3)
    linarith
    apply Eq.le
    symm
    apply Polynomial.natDegree_X_pow_sub_C
  . apply Eq.le
    apply Polynomial.natDegree_X_pow_sub_C

lemma degree_third_root_of_two : Polynomial.degree (minpoly ℚ ((2:ℂ ) ^ (1/3:ℂ))) = 3 := by
  have h: minpoly ℚ ((2:ℂ ) ^ (1/3:ℂ)) = P := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    case hp1 => exact P_irreducible
    case hp2 =>
      simp[P]
    case hp3 =>
      exact P_monic
  rw[h, P, Polynomial.degree_eq_natDegree]
  norm_cast
  apply natDegree_X_pow_sub_C
  apply Polynomial.X_pow_sub_C_ne_zero
  simp


--TODO: Tidy Up
noncomputable def K_zero_P: IntermediateField ℚ ℂ := K_zero {(0:ℂ),(1:ℂ)}

--TODO: Tidy Up
lemma not_mod_eq_imp_not_eq (a b n : ℕ ) (h : ¬ a % n = b % n) : ¬ a = b := by
  exact fun a_1 ↦ h (congrFun (congrArg HMod.hMod a_1) n)


lemma third_root_of_two_not_in_M_inf: (2 : ℂ) ^ (1/3: ℂ) ∉ M_inf {(0:ℂ),(1:ℂ)} := by
  apply Classfication_z_in_M_inf_2m_not (Set.mem_insert 0 {1}) (Set.mem_insert_of_mem 0 rfl)
  simp
  intro x
  have h: ¬ 2 ^ x =  Polynomial.degree (minpoly ℚ ((2:ℂ ) ^ (1/3:ℂ))) := by
    rw[degree_third_root_of_two]
    cases x with
      | zero => simp
      | succ x => norm_cast; rw[pow_succ]; apply not_mod_eq_imp_not_eq (n:= 2); norm_num
  convert h
  simp
  have K_zero_P_eq_bot:  K_zero_P = ⊥ := by
    rw [← K_zero_eq_rational_if_M_sub_Q {0,1}]
    · rw [K_zero_P, K_zero]
    rintro _ (rfl|rfl)
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩]
  have K_P_eq_K_M: K_zero_P = K_zero {(0:ℂ),(1:ℂ)} := by
    rw [K_zero_P_eq_bot, K_zero_eq_rational_if_M_sub_Q {(0:ℂ),(1:ℂ)}]
    have: {0,(1:ℂ)} ⊆ Set.range Rat.cast:= by
      rintro _ (rfl|rfl)
      exacts [⟨0, by simp⟩, ⟨1, by simp⟩]
    exact this
  rw[K_P_eq_K_M] at K_zero_P_eq_bot
  rw [minpoly.map_of_isScalarTower ℚ (K_zero {(0:ℂ),(1:ℂ)}), Polynomial.degree_map]
  rw [K_zero_P_eq_bot]
  exact (IntermediateField.botEquiv ℚ ℂ).symm.bijective
