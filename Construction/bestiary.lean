import Construction.Chapter1.basic_construction
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.IntermediateField
import Mathlib.FieldTheory.Adjoin



/- -- TODO: Find out if needed and how to use
structure M where
  (M : Set ℂ)
  (M_0 : ↑(0:ℂ)  ∈ ↑M)
  (M_1 : 1 ∈ M)
 -/


open Polynomial
open FiniteDimensional Polynomial
open scoped Classical Polynomial

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
