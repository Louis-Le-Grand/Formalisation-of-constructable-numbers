import Construction.Chapter2.MField
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.IntermediateField
import Mathlib.FieldTheory.Adjoin
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real



/- -- TODO: Find out if needed and how to use
structure M where
  (M : Set ℂ)
  (M_0 : ↑(0:ℂ)  ∈ ↑M)
  (M_1 : 1 ∈ M)
 -/


open Polynomial
open FiniteDimensional Polynomial
open scoped Classical Polynomial
--https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Polynomial.20irreducible/near/412616130
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

lemma real_component_in_M_inf(M : Set ℂ):  x.re ∉ M_inf M → x ∉ M_inf M := by sorry

noncomputable def K_zero (M : Set ℂ) : IntermediateField ℚ  ℂ := IntermediateField.adjoin ℚ ({(z : ℂ)  | z ∈ M} ∪ {(starRingEnd ℂ) z  | z ∈ M})

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

lemma not_mod_eq_imp_not_eq (a b n : ℕ ) (h : ¬ a % n = b % n) : ¬ a = b := by
  intro h'
  rw[h'] at h
  simp at h

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
