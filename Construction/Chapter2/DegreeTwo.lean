import Mathlib.FieldTheory.Adjoin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open IntermediateField Polynomial

section degree_two

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
variable (K : IntermediateField F E) (L : IntermediateField K E)

private lemma minpoly_two_le_iff {x : E} (hx : IsIntegral K x) :
    2 ≤ (minpoly K x).natDegree ↔ x ∉ K := by
  simpa only [RingHom.mem_range, IntermediateField.algebraMap_apply,
    Subtype.exists, exists_prop, exists_eq_right] using minpoly.two_le_natDegree_iff hx

theorem dergree_two_rank_two :
    FiniteDimensional.finrank K L = 2 ↔
      ∃ x : E, L = IntermediateField.adjoin K {x} ∧ (minpoly K x).natDegree = 2 := by
  constructor
  · intro hdim
    letI : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (by omega)
    have hnot : ¬ L ≤ ⊥ := by
      intro h
      have hL : L = ⊥ := le_antisymm h bot_le
      have hone : FiniteDimensional.finrank K L = 1 :=
        IntermediateField.finrank_eq_one_iff.mpr hL
      omega
    obtain ⟨x, hxL, hxK⟩ := SetLike.not_le_iff_exists.mp hnot
    have hxK' : x ∉ K := by
      simpa only [IntermediateField.mem_bot, Set.mem_range,
        IntermediateField.algebraMap_apply, Subtype.exists, exists_prop,
        exists_eq_right] using hxK
    have hx : IsIntegral K x := (IsIntegral.of_finite K (⟨x, hxL⟩ : L)).map L.val
    have hdle : (minpoly K x).natDegree ≤ 2 := by
      have h := minpoly.natDegree_le (K := K) (⟨x, hxL⟩ : L)
      rw [← minpoly.algHom_eq L.val L.val.injective (⟨x, hxL⟩ : L)] at h
      simpa only [hdim] using h
    have hd : (minpoly K x).natDegree = 2 :=
      le_antisymm hdle ((minpoly_two_le_iff K hx).mpr hxK')
    refine ⟨x, ?_, hd⟩
    apply Eq.symm
    apply IntermediateField.eq_of_le_of_finrank_le
    · exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxL)
    · rw [IntermediateField.adjoin.finrank hx, hd, hdim]
  · rintro ⟨x, rfl, hd⟩
    have hx : IsIntegral K x := by
      by_contra h
      rw [minpoly.eq_zero h] at hd
      simp at hd
    rw [IntermediateField.adjoin.finrank hx, hd]

theorem dergree_two_eq_sqr [CharZero K] :
    FiniteDimensional.finrank K L = 2 ↔
      ∃ x : E, x ^ 2 ∈ K ∧ x ∉ K ∧ L = IntermediateField.adjoin K {x} := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  rw [dergree_two_rank_two K L]
  constructor
  · rintro ⟨x, hL, hd⟩
    have hx : IsIntegral K x := by
      by_contra h
      rw [minpoly.eq_zero h] at hd
      simp at hd
    have hxK : x ∉ K := (minpoly_two_le_iff K hx).mp (by omega)
    let b : K := (minpoly K x).coeff 1
    let c : K := (minpoly K x).coeff 0
    have hp : minpoly K x = X ^ 2 + C b * X + C c := by
      have hp := (minpoly K x).as_sum_range_C_mul_X_pow
      rw [hd] at hp
      have hc : (minpoly K x).coeff 2 = 1 := by
        rw [← hd]
        exact (minpoly.monic hx).coeff_natDegree
      simpa [Finset.sum_range_succ, hc, b, c, add_comm, add_left_comm, add_assoc] using hp
    have hroot : x ^ 2 + (b : E) * x + (c : E) = 0 := by
      have h := minpoly.aeval K x
      rw [hp] at h
      simpa using h
    let y : E := 2 * x + b
    have hy_sq : y ^ 2 = ((b ^ 2 - 4 * c : K) : E) := by
      change (2 * x + (b : E)) ^ 2 = (b : E) ^ 2 - 4 * (c : E)
      linear_combination 4 * hroot
    have h2 : (2 : E) ≠ 0 := by norm_num
    have hxy : x = (y - (b : E)) / 2 := by
      dsimp [y]
      field_simp
    have hyK : y ∉ K := by
      intro hy
      apply hxK
      rw [hxy]
      exact K.div_mem (K.sub_mem hy b.property) (K.natCast_mem 2)
    refine ⟨y, ?_, hyK, hL.trans ?_⟩
    · rw [hy_sq]
      exact (b ^ 2 - 4 * c).property
    · apply le_antisymm
      · apply IntermediateField.adjoin_le_iff.mpr
        apply Set.singleton_subset_iff.mpr
        rw [hxy]
        exact div_mem (sub_mem (IntermediateField.mem_adjoin_simple_self K y)
          ((IntermediateField.adjoin K {y}).algebraMap_mem b))
          (IntermediateField.natCast_mem _ 2)
      · apply IntermediateField.adjoin_le_iff.mpr
        apply Set.singleton_subset_iff.mpr
        exact add_mem (mul_mem (IntermediateField.natCast_mem _ 2)
          (IntermediateField.mem_adjoin_simple_self K x))
          ((IntermediateField.adjoin K {x}).algebraMap_mem b)
  · rintro ⟨x, hsq, hxK, hL⟩
    let a : K := ⟨x ^ 2, hsq⟩
    have hm : (X ^ 2 - C a : K[X]).Monic := monic_X_pow_sub_C a (by decide)
    have hr : aeval x (X ^ 2 - C a : K[X]) = 0 := by simp [a]
    have hx : IsIntegral K x := ⟨X ^ 2 - C a, hm, hr⟩
    refine ⟨x, hL, le_antisymm ?_ ((minpoly_two_le_iff K hx).mpr hxK)⟩
    have h := Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero K x hm.ne_zero hr)
    simpa using h

end degree_two
