import Mathlib

open Polynomial
open FiniteDimensional Polynomial
/-
no goals to be solved
-/
open scoped Classical Polynomial

--! This is a test whit use using ℂs and instead Complex numbers

def G (z₁ z₂ : ℂ): Set ℂ := {z : ℂ | ∃ r : ℝ, z = ((r : ℂ) * z₁ + 1 - r * z₂)}
def C (z₁ : ℂ) (r : ℝ): Set ℂ := {z : ℂ | (z.re - z₁.re) ^ 2 + ( z.im -  z₁.im) ^ 2 = r}

def Z_one_M (M : Set ℂ) : Set ℂ := {z : ℂ| ∃ z₁ z₂ z₃ z₄ : ℂ,  z ∈ (G z₁ z₂ ∩ G z₃ z₄) ∧ z₁ ≠ z₃ ∧ z₁ ≠ z₄ ∧ z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M}
def Z_two_M (M : Set ℂ) : Set ℂ := {z : ℂ| ∃ z₁ z₂ z₃ z₄ z₅ : ℂ,  z ∈ (G z₁ z₂ ∩ C z₃ (Complex.normSq (z₄ -  z₅))) ∧ z₄ ≠ z₅ ∧  z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M ∧ z₅ ∈ M}
def Z_three_M (M : Set ℂ) : Set ℂ := {z : ℂ| ∃ z₁ z₂ z₃ z₄ z₅ z₆ : ℂ,  z ∈ (C z₁ (Complex.normSq (z₂ -  z₃)) ∩ C z₄ (Complex.normSq (z₅ -  z₆))) ∧ z₁ ≠ z₄ ∧ z₂ ≠ z₃ ∧ z₅ ≠ z₆ ∧ z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M ∧ z₅ ∈ M ∧ z₆ ∈ M}

def ICL_M (M : Set ℂ) : Set ℂ := M ∪ Z_one_M M ∪ Z_two_M M ∪ Z_three_M M

def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => ICL_M (M_I M n)

def M_inf (M : Set ℂ) : Set ℂ := ⋃ n : ℕ, M_I M n

noncomputable def K_zero (M : Set ℂ) : IntermediateField ℚ  ℂ := IntermediateField.adjoin ℚ ({(z : ℂ)  | z ∈ M} ∪ {(starRingEnd ℂ) z  | z ∈ M})

lemma real_component_in_M_inf(M : Set ℂ):  x.re ∉ M_inf M → x ∉ M_inf M := by sorry


theorem Classfication_z_in_M_inf (M : Set ℂ) (z : ℂ) :
z ∈ M_inf M ↔
  ∃ (n : ℕ) (L : ℕ →  (IntermediateField ℚ ℂ)) (H : ∀ i,  Module (L i) (L (i + 1))),
  z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, FiniteDimensional.finrank (L i) (L (i + 1)) = 2) := by
  constructor
  case mp =>
    intro h
    sorry
  case mpr => sorry

lemma Classfication_z_in_M_inf_2m (M : Set ℂ) (z : ℂ) :
  z ∈ M_inf M →  ∃ (m : ℕ) ,((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z)  := by
    intro h
    rw [Classfication_z_in_M_inf] at h
    obtain ⟨n, L, H, h₁, h₂, h₃⟩ := h
    sorry

lemma short (M : Set ℂ) (z : ℂ) :
  ¬ (∃ (m : ℕ) ,((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z)) → z ∉ M_inf M := by
    apply Not.imp_symm
    simp
    apply Classfication_z_in_M_inf_2m


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
    simp at hy
    obtain ⟨q, hq₁, hq₂⟩ := hy
    rw[←hq₂, h']
    exact h hq₁
    exact hq₁
  . simp

--lemma mini_polynom_dergree_eq_iff (L: Type)[Field L](L₁ L₂: Subfield L)(α : L): (L₁  = L₂) → degree (minpoly L₁ α) = degree (minpoly L₂ α) := by sorry
--#check IntermediateField.adjoin_le_iff

--! This is are helper lemmas to show irreducibility of polynomials: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Polynomial.20irreducible/near/412616130
theorem irreducible_iff_lt_natDegree_lt {R} [CommSemiring R] [NoZeroDivisors R]
    {p : R[X]} (hp : p.Monic) (hp1 : p ≠ 1) :
    Irreducible p ↔ ∀ q, Monic q → natDegree q ∈ Finset.Ioc 0 (natDegree p / 2) → ¬ q ∣ p := by
  rw [hp.irreducible_iff_natDegree', and_iff_right hp1]
  constructor
  · rintro h g hg hdg ⟨f, rfl⟩
    exact h f g (hg.of_mul_monic_left hp) hg (mul_comm f g) hdg
  · rintro h f g - hg rfl hdg
    exact h g hg hdg (dvd_mul_left g f)

theorem irreducible_iff_roots_eq_zero_of_degree_le_three {R} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : p.Monic)
    (hp2 : 2 ≤ p.natDegree) (hp3 : p.natDegree ≤ 3) : Irreducible p ↔ p.roots = 0 := by
  rw [irreducible_iff_lt_natDegree_lt hp]; swap
  · rintro rfl; rw [natDegree_one] at hp2; cases hp2
  have hp0 : p ≠ 0 := by rintro rfl; rw [natDegree_zero] at hp2; cases hp2
  simp_rw [show p.natDegree / 2 = 1 from (Nat.div_le_div_right hp3).antisymm
    (by apply Nat.div_le_div_right (c := 2) hp2), show Finset.Ioc 0 1 = {1} from rfl,
    Finset.mem_singleton, Multiset.eq_zero_iff_forall_not_mem, mem_roots hp0, ← dvd_iff_isRoot]
  refine ⟨fun h r ↦ h _ (monic_X_sub_C r) (natDegree_X_sub_C r), fun h q hq hq1 ↦ ?_⟩
  rw [hq.eq_X_add_C hq1, ← sub_neg_eq_add, ← C_neg]; apply h

--Zulip: https://live.lean-lang.org/#code=import%20Mathlib%0A%0Anoncomputable%20def%20K_zero%20(M%3A%20Set%20ℂ)%3A%20IntermediateField%20ℚ%20ℂ%20%3A%3D%20IntermediateField.adjoin%20ℚ%20(M%20∪%20%7B(starRingEnd%20ℂ)%20z%20%20%7C%20z%20∈%20M%7D)%0Anoncomputable%20def%20K_zero_P%20%3A%20IntermediateField%20ℚ%20ℂ%20%3A%3D%20IntermediateField.adjoin%20ℚ%20%7B(0%3Aℂ)%2C(1%3Aℂ)%7D%0A%0A--%20What%20if%20have%20showed%20and%20want%20to%20use%0Alemma%20K_zero_eq_rational_if_M_sub_Q%20(M%20%3A%20Set%20ℂ)%20(h%20%3A%20M%20⊆%20Set.range%20((↑)%3A%20ℚ%20→%20ℂ))%20%3A%20K_zero%20M%20%3D%20⊥%20%3A%3D%20by%20sorry%0A%0Alemma%20K_zero_P_eq_bot%20%3A%20K_zero_P%20%3D%20⊥%20%3A%3D%20by%0A%20%20rw%20%5B←%20K_zero_eq_rational_if_M_sub_Q%20%7B0%2C1%7D%5D%0A%20%20·%20rw%20%5BK_zero_P%2C%20K_zero%5D%3B%20congr%0A%20%20%20%20convert%20(Set.union_self%20_).symm%20using%202%0A%20%20%20%20ext%3B%20simp%20%5Beq_comm%5D%0A%20%20rintro%20_%20(rfl%7Crfl)%0A%20%20exacts%20%5B⟨0%2C%20by%20simp⟩%2C%20⟨1%2C%20by%20simp⟩%5D%0A%0Asection%0Avariable%20%7BM%20N%20F%7D%20%5BMonoid%20M%5D%20%5BMonoid%20N%5D%20%5BEquivLike%20F%20M%20N%5D%20%5BMulEquivClass%20F%20M%20N%5D%20(f%20%3A%20F)%20%7Bm%20%3A%20M%7D%0A%0Atheorem%20map_isUnit_iff%20%3A%20IsUnit%20(f%20m)%20↔%20IsUnit%20m%20%3A%3D%0A%20%20⟨by%20convert%20←%20IsUnit.map%20(MulEquivClass.toMulEquiv%20f).symm%3B%20apply%20EquivLike.left_inv%2C%20IsUnit.map%20f⟩%0A%0Atheorem%20map_irreducible_iff%20%3A%20Irreducible%20(f%20m)%20↔%20Irreducible%20m%20%3A%3D%20by%0A%20%20simp_rw%20%5Birreducible_iff%2C%20(EquivLike.surjective%20f).forall%2C%20←%20map_mul%2C%20(EquivLike.injective%20f).eq_iff%2C%20map_isUnit_iff%5D%0A%0Aend%0A%0A--%20%60IsDomain%20R%60%20can%20probably%20be%20removed%20using%20docs%23minpoly.unique%0Atheorem%20minpoly.map_of_isScalarTower%20(A%20K)%20%7BR%7D%20%5BField%20A%5D%20%5BField%20K%5D%20%5BRing%20R%5D%20%5BIsDomain%20R%5D%20%5BAlgebra%20A%20K%5D%0A%20%20%20%20%5BAlgebra%20A%20R%5D%20%5BAlgebra%20K%20R%5D%20%5BIsScalarTower%20A%20K%20R%5D%20(h%20%3A%20Function.Bijective%20(algebraMap%20A%20K))%20(x%20%3A%20R)%20%3A%0A%20%20%20%20minpoly%20K%20x%20%3D%20(minpoly%20A%20x).map%20(algebraMap%20A%20K)%20%3A%3D%20by%0A%20%20by_cases%20h0%20%3A%20IsIntegral%20A%20x%0A%20%20·%20symm%3B%20apply%20minpoly.eq_of_irreducible_of_monic%0A%20%20%20%20·%20rw%20%5Bshow%20algebraMap%20A%20K%20%3D%20RingEquiv.ofBijective%20_%20h%20from%20rfl%2C%20←%20Polynomial.mapEquiv_apply%2C%20map_irreducible_iff%5D%0A%20%20%20%20%20%20exact%20minpoly.irreducible%20h0%0A%20%20%20%20·%20simp%0A%20%20%20%20·%20exact%20(minpoly.monic%20h0).map%20_%0A%20%20·%20rw%20%5Bminpoly.eq_zero%20h0%2C%20Polynomial.map_zero%5D%0A%20%20%20%20exact%20minpoly.eq_zero%20(mt%20(isIntegral_trans%20(Algebra.isIntegral_of_surjective%20h.surjective)%20_%20·)%20h0)%0A%0Alemma%20H%20%3A%20Polynomial.degree%20((minpoly%20↑K_zero_P)%20(2%20%5E%20(3%3Aℂ)⁻¹%20%3Aℂ))%20%3D%20Polynomial.degree%20(minpoly%20ℚ%20(2%20%5E%20(3%3Aℂ)⁻¹%20%3Aℂ))%20%3A%3D%20by%0A%20%20rw%20%5Bminpoly.map_of_isScalarTower%20ℚ%20K_zero_P%2C%20Polynomial.degree_map%5D%0A%20%20rw%20%5BK_zero_P_eq_bot%5D%0A%20%20exact%20(IntermediateField.botEquiv%20ℚ%20ℂ).symm.bijective%0A
section
variable {M N F} [Monoid M] [Monoid N] [EquivLike F M N] [MulEquivClass F M N] (f : F) {m : M}

theorem map_isUnit_iff : IsUnit (f m) ↔ IsUnit m :=
  ⟨by convert ← IsUnit.map (MulEquivClass.toMulEquiv f).symm; apply EquivLike.left_inv, IsUnit.map f⟩

theorem map_irreducible_iff : Irreducible (f m) ↔ Irreducible m := by
  simp_rw [irreducible_iff, (EquivLike.surjective f).forall, ← map_mul, (EquivLike.injective f).eq_iff, map_isUnit_iff]

end

theorem minpoly.map_of_isScalarTower (A K) {R} [Field A] [Field K] [Ring R] [IsDomain R] [Algebra A K]
    [Algebra A R] [Algebra K R] [IsScalarTower A K R] (h : Function.Bijective (algebraMap A K)) (x : R) :
    minpoly K x = (minpoly A x).map (algebraMap A K) := by
  by_cases h0 : IsIntegral A x
  · symm; apply minpoly.eq_of_irreducible_of_monic
    · rw [show algebraMap A K = RingEquiv.ofBijective _ h from rfl, ← Polynomial.mapEquiv_apply, map_irreducible_iff]
      exact minpoly.irreducible h0
    · simp
    · exact (minpoly.monic h0).map _
  · rw [minpoly.eq_zero h0, Polynomial.map_zero]
    exact minpoly.eq_zero (mt (isIntegral_trans (Algebra.isIntegral_of_surjective h.surjective) _ ·) h0)

--section constructionDoubleCube
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
  rw[irreducible_iff_roots_eq_zero_of_degree_le_three P_monic]
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

lemma not_mod_eq_imp_not_eq (a b n : ℕ ) (h : ¬ a % n = b % n) : ¬ a = b := by
  intro h'
  rw[h'] at h
  simp at h

--TODO: Tidy Up
noncomputable def K_zero_P: IntermediateField ℚ ℂ := K_zero {(0:ℂ),(1:ℂ)}

lemma third_root_of_two_not_in_M_inf (M := {(0:ℂ),(1:ℂ)}): (2 : ℂ) ^ (1/3: ℂ) ∉ M_inf M := by
  apply short
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
  have K_P_eq_K_M: K_zero_P = K_zero M := by
    rw [K_zero_P_eq_bot, K_zero_eq_rational_if_M_sub_Q M]
    have: {0,(1:ℂ)} ⊆ Set.range Rat.cast:= by
      rintro _ (rfl|rfl)
      exacts [⟨0, by simp⟩, ⟨1, by simp⟩]
    have M_eqq: M = {0,(1:ℂ)} := by sorry
    rw[←M_eqq] at this
    exact this
  rw[K_P_eq_K_M] at K_zero_P_eq_bot
  rw [minpoly.map_of_isScalarTower ℚ (K_zero M), Polynomial.degree_map]
  rw [K_zero_P_eq_bot]
  exact (IntermediateField.botEquiv ℚ ℂ).symm.bijective

--end constructionDoubleCube


--section constructionAngleTrisection
open Polynomial IsFractionRing

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
  rw[irreducible_iff_roots_eq_zero_of_degree_le_three HM]
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
end

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

lemma pi_third_not_in_M_inf (M := {⟨0,0⟩ ,⟨1,0⟩,  Complex.exp (Complex.I *Real.pi/3) }) :
  (Complex.exp (Complex.I * (Real.pi/3)/3) : ℂ) ∉ M_inf M := by
  apply real_component_in_M_inf
  apply short
  simp
  intro x
  have h: ↑(Complex.exp (Complex.I * (↑Real.pi / 3) / 3)).re = (Real.cos ((Real.pi/3)/3): ℂ):= by sorry
  rw[h]
  have h: ¬ 2 ^ x =  Polynomial.degree (minpoly ℚ ((Real.cos ((Real.pi/3)/3)): ℂ)) := by
    rw[exp_pi_ninth]
    cases x with
      | zero => simp
      | succ x => norm_cast; rw[pow_succ]; apply not_mod_eq_imp_not_eq (n:= 2); norm_num
  convert h
  sorry

variable (α : ℂ)
lemma Angle_not_Trisectable(M := {⟨0,0⟩ ,⟨1,0⟩, Complex.exp (Complex.I * α)}) :
  ∃ (α : ℂ), (Complex.exp (Complex.I * α/3) : ℂ) ∉ M_inf M := by
  use (Real.pi/3)
  exact pi_third_not_in_M_inf M

--end constructionAngleTrisection
