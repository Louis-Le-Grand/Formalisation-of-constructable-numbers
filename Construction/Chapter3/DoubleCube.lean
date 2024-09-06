import Construction.Chapter2.ClasificationMinf
import Construction.NotMyCode.map_of_isScalarTower

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Real.Irrational

open Construction Polynomial

noncomputable def P : (Polynomial ℚ) := X ^ 3 - Polynomial.C 2 -- x^3 - 2

lemma P_monic: Monic P := by
  refine monic_of_natDegree_le_of_coeff_eq_one 3 (Eq.le Polynomial.natDegree_X_pow_sub_C) ?_
  simp only [P, coeff_sub, coeff_X_pow, ↓reduceIte, coeff_C_succ, sub_zero]

lemma irrational_thirdroot_two: Irrational (2 ^ (1/3:ℝ)) := by
  apply irrational_nrt_of_notint_nrt 3 2 ?_ ?_ (Nat.zero_lt_succ 2)
  . simp only [one_div, Int.cast_ofNat]
    exact @Real.rpow_inv_natCast_pow 2 3 zero_le_two (Ne.symm (Nat.zero_ne_add_one 2))
  . rw [Mathlib.Tactic.PushNeg.not_exists_eq]
    intro x
    by_contra h
    have: ¬ x ≤ (1:ℝ)  := by
      rw[←lt_iff_not_le, ←h, @Real.one_lt_rpow_iff 2 (1/3) zero_le_two]
      norm_num
    have: x < (2:ℝ)  := by
      rw[←Real.rpow_one 2, ←h, @Real.rpow_lt_rpow_left_iff 2 (1/3:ℝ) (1:ℝ) one_lt_two]
      norm_num
    norm_cast at *
    rw [←Int.le_sub_one_iff] at this
    ring_nf at this
    contradiction

lemma if_cube_eq_two_irrat (x:ℝ): x ^ 3 = 2 → Irrational x := by
  intro h
  have h₁: 0 ≤ x := by
    rw[←Odd.pow_nonneg_iff (n:=3) (Nat.odd_iff.mpr rfl), h]
    linarith
  have h₂: 2 ^ (3⁻¹:ℝ) = x := by
    rw[Real.rpow_inv_eq zero_le_two h₁ (Ne.symm (NeZero.ne' 3)), ←h]
    norm_cast
  rw[←h₂, inv_eq_one_div]
  exact irrational_thirdroot_two

lemma P_roots: roots P = 0 := by
  refine Multiset.eq_zero_of_forall_not_mem ?_
  simp only [P, mem_roots', ne_eq, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, not_and]
  intros a _
  by_contra h
  rw[sub_eq_zero] at h
  have h: (a:ℝ)^3 = 2 := by
    norm_cast
  exact if_cube_eq_two_irrat a h (Set.mem_range_self a)

lemma P_irreducible : Irreducible P := by
  rw[irreducible_iff_roots_eq_zero_of_degree_le_three]
  . exact P_roots
  . refine le_trans (b:=3) Nat.AtLeastTwo.prop (Eq.le ?_)
    symm
    exact Polynomial.natDegree_X_pow_sub_C
  . exact Eq.le Polynomial.natDegree_X_pow_sub_C

lemma degree_third_root_of_two : Polynomial.degree (minpoly ℚ ((2:ℂ ) ^ (1/3:ℂ))) = 3 := by
  have h: P = minpoly ℚ ((2:ℂ ) ^ (1/3:ℂ)) := by
    refine minpoly.eq_of_irreducible_of_monic P_irreducible ?_ P_monic
    simp only [one_div, P, map_sub, map_pow, aeval_X, Complex.cpow_ofNat_inv_pow, aeval_C,
      eq_ratCast, Rat.cast_ofNat, sub_self]
  rw[←h, P, Polynomial.degree_eq_natDegree (X_pow_sub_C_ne_zero (Nat.zero_lt_succ 2) 2)]
  norm_cast
  exact natDegree_X_pow_sub_C

--TODO: Tidy Up
lemma not_mod_eq_imp_not_eq (a b n : ℕ ) (h : ¬ a % n = b % n) : ¬ a = b := by
  exact fun a_1 ↦ h (congrFun (congrArg HMod.hMod a_1) n)

lemma third_root_of_two_not_in_M_inf: (2 : ℂ) ^ (1/3: ℂ) ∉ M_inf {(0:ℂ),(1:ℂ)} := by
  apply Classfication_z_in_M_inf_2m_not (Set.mem_insert 0 {1}) (Set.mem_insert_of_mem 0 rfl)
  simp only [Nat.cast_ofNat, one_div, not_exists]
  intro x
  have h: ¬ 2 ^ x =  Polynomial.degree (minpoly ℚ ((2:ℂ ) ^ (1/3:ℂ))) := by
    rw[degree_third_root_of_two]
    cases x with
      | zero => simp
      | succ x => norm_cast; rw[pow_succ]; apply not_mod_eq_imp_not_eq (n:= 2); norm_num
  convert h
  have: K_zero {(0:ℂ),(1:ℂ)} = ⊥ := by
    rw [← K_zero_eq_rational_if_M_sub_Q {0,1}]
    rintro _ (rfl|rfl)
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩]
  rw [one_div, minpoly.map_of_isScalarTower ℚ _, Polynomial.degree_map]
  rw[this]
  exact (IntermediateField.botEquiv ℚ ℂ).symm.bijective
