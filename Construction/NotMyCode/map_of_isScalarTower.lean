import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

section
--Zulip: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20Degree.20polynomial.20Q.5BX.5D.20.3D.20K.5BX.5D/near/420593608
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
    apply minpoly.eq_zero (mt (?_) h0)
    apply @isIntegral_trans _  K _ _ _ _ _ _ _ _ (Algebra.isIntegral_of_surjective h.surjective) x
end
