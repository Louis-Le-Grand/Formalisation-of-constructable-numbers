import Construction.Chapter1.basic_construction
import Mathlib.FieldTheory.Adjoin

open Construction
noncomputable def MField (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): Subfield ℂ := {
  carrier := M_inf M
  zero_mem' := by exact M_M_inf M h₀
  one_mem' := by exact M_M_inf M h₁
  add_mem' := by apply add_M_Inf M h₀
  neg_mem' := by apply z_neg_M_inf M h₀
  mul_mem' := by apply mul_M_inf M h₀ h₁
  inv_mem' := by apply inv_M_inf M h₀ h₁
}

--? TODO: Add to blueprint
lemma MField_mem (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): ∀ x : ℂ, x ∈ MField M h₀ h₁ ↔ x ∈ M_inf M := by
  intro x
  exact @Subfield.mem_carrier ℂ _ (MField M h₀ h₁) x

lemma MField_i (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): Complex.I ∈ MField M h₀ h₁ := by
  exact imath_M_inf M h₀ h₁

--? TODO: Add to blueprint
lemma MField_i_mul (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): ∀ x : ℝ, ↑x ∈ MField M h₀ h₁ ↔
    Complex.I * x ∈ MField M h₀ h₁ := by
  intro x
  constructor
  exact @Subfield.mul_mem ℂ _ (MField M h₀ h₁) (Complex.I) x (MField_i M h₀ h₁)
  exact i_z_imp_z_in_M_inf M h₀ h₁ x

lemma MField_re_im (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): ∀ x : ℂ, x ∈ MField M h₀ h₁ ↔
    ↑x.re ∈ MField M h₀ h₁ ∧ ↑x.im ∈ MField M h₀ h₁ := by
  exact z_iff_re_im_M_inf M h₀ h₁

lemma MField_re_im' (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): ∀ x : ℂ, x ∈ MField M h₀ h₁ ↔
    ↑x.re ∈ MField M h₀ h₁ ∧ Complex.I * x.im ∈ MField M h₀ h₁ := by
  intro x
  rw[←MField_i_mul M h₀ h₁]
  exact z_iff_re_im_M_inf M h₀ h₁ x

lemma MField_polar (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M): ∀ x : ℂ, x ∈ MField M h₀ h₁ ↔
    ↑(Complex.abs x) ∈ MField M h₀ h₁ ∧ Complex.exp (Complex.arg x * Complex.I) ∈  MField M h₀ h₁ := by
  intro x
  constructor
  . intro hx
    constructor
    apply abs_M_Inf M h₀ h₁ x hx
    apply angle_M_inf M h₀ h₁ x hx
  intro hx
  obtain ⟨habs, hang⟩ := hx
  rw[←Complex.abs_mul_exp_arg_mul_I x]
  apply mul_M_inf M h₀ h₁ _ _ habs hang

class QuadraticClosed (F: Type*) [Field F] : Prop where
  exists_root: ∀ x : F, ∃ y : F, y * y = x

instance MField_QuadraticClosed (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M) :
    QuadraticClosed (MField M h₀ h₁) where
  exists_root := by
    intro x
    rw[Subtype.exists]
    use (↑(Complex.abs x) ^ (1/2:ℂ) * ((↑ (Complex.arg x)/(2:ℂ) * Complex.I).exp))
    constructor
    rw[←pow_two]
    simp only [one_div, SubmonoidClass.mk_pow, Complex.cpow_ofNat_inv_pow, Subtype.coe_eta]
    simp_rw[pow_two]
    ring_nf
    norm_cast
    simp_rw[←Complex.exp_nat_mul (↑(x:ℂ).arg * Complex.I * (1 / 2)) 2]
    simp only [one_div, Complex.cpow_ofNat_inv_pow, Nat.cast_ofNat]
    ring_nf
    simp only [Complex.abs_mul_exp_arg_mul_I, Subtype.coe_eta]
    exact root_M_inf M h₀ h₁ x (by rw[←MField_mem M h₀ h₁ x]; simp only [SetLike.coe_mem])

lemma MField_QuadraticClosed_def (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M) {x : ℂ} (h: x ∈ (MField M h₀ h₁)): ∃ y : (MField M h₀ h₁), y * y = x := by
  have: ∃ x' : (MField M h₀ h₁), x' = x := by
    exact CanLift.prf x h
  obtain ⟨x', hx'⟩ := this
  rw[← hx']
  norm_cast
  exact QuadraticClosed.exists_root x'

def conj_set (M : Set ℂ) : Set ℂ := {starRingEnd ℂ z | z ∈ M}

lemma conj_union (M N : Set ℂ) : conj_set (M ∪ N) = conj_set M ∪ conj_set N := by
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  intro h
  obtain ⟨z, hz, hX⟩ := h
  cases hz with | inl => left; use z | inr => right; use z
  intro h
  cases h with | inl h => obtain ⟨z, hz, hX⟩ := h; exact ⟨z, Or.intro_left _ hz, hX⟩ | inr h =>
    obtain ⟨z, hz, hX⟩ := h; exact ⟨z, Or.intro_right _ hz, hX⟩


lemma conj_conj_id (M : Set ℂ) : conj_set (conj_set M) = M := by
  simp only [Set.mem_setOf_eq, exists_exists_and_eq_and, RingHomCompTriple.comp_apply,
    RingHom.id_apply, exists_eq_right, Set.setOf_mem_eq, conj_set]

class ConjClosed (M : Set ℂ) : Prop where
  equal: M = conj_set M

--def IsConjectClosed (M: Set ℂ) :=  M = conj_set M

-- lemma sub_conj_conjclosed (M N: Set ℂ) [ConjClosed M] : conj_set N ⊆ M ↔ N ⊆ M := by
--   sorry

instance MField_conj (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1∈ M) : ConjClosed (MField M h₀ h₁) where
  equal := by
    unfold conj_set
    rw [@Set.Subset.antisymm_iff]
    constructor
    . rw [@Set.subset_setOf]
      intro x hx
      use (starRingEnd ℂ) x
      constructor
      . simp only [SetLike.mem_coe]
        apply conj_M_Inf M h₀ h₁ x (by rw[←MField_mem M h₀ h₁ x]; norm_cast)
      . simp only [RingHomCompTriple.comp_apply, RingHom.id_apply]
    . rw [@Set.setOf_subset]
      intro x hx
      simp only [SetLike.mem_coe]
      obtain ⟨y, hy, hx⟩ := hx
      rw [←hx]
      apply conj_M_Inf M h₀ h₁ y hy
namespace ConjClosed
open ComplexConjugate

lemma M_con_M (M :Set ℂ): ConjClosed (M ∪ (conj_set M)) where
  equal := by rw[conj_union, conj_conj_id, Set.union_comm]

lemma Rat_ConjClosed : ConjClosed {x:ℂ|∃q:ℚ, ↑q = x} where
  equal := by simp only [conj_set, Set.mem_setOf_eq, exists_exists_eq_and, map_ratCast]

lemma Rat_ConjClosed' : ConjClosed (⊥: IntermediateField ℚ ℂ) where
  equal := by
    ext x
    simp only [SetLike.mem_coe, IntermediateField.mem_bot, Set.mem_range, eq_ratCast, conj_set,
      exists_exists_eq_and, map_ratCast, Set.mem_setOf_eq]

variable (M : Set ℂ) [ConjClosed M]

lemma conj_L (z : ℂ) (h : z ∈ M): conj z ∈ M := by
  have: conj z ∈ conj_set M := by
    simp only [conj_set, SetLike.mem_coe, Set.mem_setOf_eq]
    use z
  rw[←ConjClosed.equal] at this
  exact this


lemma conj_L' (z : ℂ) (h : conj z  ∈ M):  z ∈ M := by
  have: z ∈ conj_set M := by
    simp only [conj_set, SetLike.mem_coe, Set.mem_setOf_eq]
    refine ⟨(conj z),h ,RCLike.conj_conj z⟩
  rw[←ConjClosed.equal] at this
  exact this

lemma conj_inclusion {M N : Set ℂ} (h: N ⊆ M): conj_set N ⊆ conj_set M := by
  simp only [conj_set, Set.setOf_subset_setOf, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro x hx
  refine ⟨x, h hx, rfl⟩

lemma conj_mul_field {K : Subfield ℂ} {x y : ℂ} (hx: x ∈ conj_set K) (hy: y ∈ conj_set K): x * y ∈ conj_set K := by
  simp_all only [conj_set, Set.mem_setOf_eq]
  obtain ⟨x', hx', hx⟩ := hx
  obtain ⟨y', hy', hy⟩ := hy
  refine ⟨x' * y', mul_mem hx' hy', ?_⟩
  simp_all only [SetLike.mem_coe, map_mul]

lemma conj_one_field {K : Subfield ℂ} : 1 ∈ conj_set K := by
  simp only [conj_set, Set.mem_setOf_eq]
  refine ⟨1, Subfield.one_mem K, Complex.conj_eq_iff_re.mpr rfl⟩

lemma conj_add_field {K : Subfield ℂ} {x y : ℂ} (hx: x ∈ conj_set K) (hy: y ∈ conj_set K): x + y ∈ conj_set K := by
  simp_all only [conj_set, Set.mem_setOf_eq]
  obtain ⟨x', hx', hx⟩ := hx
  obtain ⟨y', hy', hy⟩ := hy
  refine ⟨x' + y', add_mem hx' hy', ?_⟩
  simp_all only [SetLike.mem_coe, map_add]

lemma conj_zero_field {K : Subfield ℂ} : 0 ∈ conj_set K := by
  simp only [conj_set, Set.mem_setOf_eq]
  refine ⟨0, Subfield.zero_mem K, Complex.conj_eq_iff_re.mpr rfl⟩

lemma conj_neg_field {K : Subfield ℂ} {x : ℂ} (hx: x ∈ conj_set K): -x ∈ conj_set K := by
  simp_all only [conj_set, Set.mem_setOf_eq]
  obtain ⟨x', hx', hx⟩ := hx
  refine ⟨-x', neg_mem hx', ?_⟩
  simp_all only [SetLike.mem_coe, map_neg]

lemma conj_inv_field {K : Subfield ℂ} {x : ℂ} (hx: x ∈ conj_set K): x⁻¹ ∈ conj_set K := by
  simp_all only [conj_set, Set.mem_setOf_eq]
  obtain ⟨x', hx', hx⟩ := hx
  refine ⟨x'⁻¹, inv_mem hx', ?_⟩
  simp_all only [SetLike.mem_coe, map_inv₀]

noncomputable def conj_field (K : Subfield ℂ) : Subfield ℂ where
  carrier := conj_set K
  mul_mem' := conj_mul_field
  one_mem' := conj_one_field
  add_mem' := conj_add_field
  zero_mem' := conj_zero_field
  neg_mem' := conj_neg_field
  inv_mem' := by apply conj_inv_field

lemma conj_restrict {K : IntermediateField ℚ ℂ} (E : IntermediateField K ℂ) [ConjClosed E]: ConjClosed (IntermediateField.restrictScalars ℚ E) where
  equal := by
    simp only [IntermediateField.coe_toSubfield, IntermediateField.coe_restrictScalars]
    exact equal

section Intersection
open Complex

lemma ill_L (l₁ l₂ : line): z ∈ l₁.points ∩ l₂.points ↔ ∃ i j : ℝ, (i:ℂ) * (l₁.z₁.re - l₁.z₂.re) + j* (l₂.z₂.re - l₂.z₁.re) = l₂.z₂.re - l₁.z₂.re ∧  i * (I*l₁.z₁.im - I*l₁.z₂.im) + j* (I*l₂.z₂.im - I*l₂.z₁.im) = I*l₂.z₂.im - I*l₁.z₂.im ∧ i * l₁.z₁ + (1 - i) * l₁.z₂ = z := by
  refine ⟨?_, ?_⟩ <;> intro h
  . simp only [line.points, Set.mem_inter_iff, Set.mem_setOf_eq] at h
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
    use i
    use j
    refine ⟨?_, ?_, hi⟩
    . rw [←hj, Complex.ext_iff] at hi
      obtain ⟨hi, _⟩ := hi
      simp only [sub_mul, one_mul, ← add_sub_assoc, Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hi
      rw [←sub_eq_zero] at hi
      simp [mul_sub, ← add_sub_assoc]
      norm_cast
      rw [←sub_eq_zero, ←hi]
      ring_nf
    . rw [←hj, Complex.ext_iff] at hi
      obtain ⟨_, hi⟩ := hi
      simp only [sub_mul, one_mul, ← add_sub_assoc, Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.ofReal_im, Complex.ofReal_re, zero_mul, sub_zero] at hi
      rw [←sub_eq_zero] at hi
      simp at hi
      simp only [mul_sub, ← add_sub_assoc]
      rw [←sub_eq_zero]
      calc _ = I * (i * l₁.z₁.im - i *  l₁.z₂.im+ j *  l₂.z₂.im - j *  l₂.z₁.im - l₂.z₂.im +  l₁.z₂.im) := by ring_nf
          _ = I * (i * l₁.z₁.im + l₁.z₂.im - i * l₁.z₂.im - (j * l₂.z₁.im + l₂.z₂.im - j * l₂.z₂.im)):= by ring_nf
          _ = 0 := by norm_cast; rw [hi]; ring_nf; simp only [ofReal_zero, mul_zero]
  obtain ⟨i, j, h₁, h₂, h₃⟩ := h
  simp only [line.points, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨⟨i, h₃⟩, ⟨j, ?_⟩⟩
  rw[←h₃]
  rw [←sub_eq_zero, ←re_add_im (↑j * l₂.z₁ + (1 - ↑j) * l₂.z₂ - (↑i * l₁.z₁ + (1 - ↑i) * l₁.z₂))]
  simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, one_re, sub_im,
    one_im, sub_self, ofReal_sub, ofReal_add, ofReal_mul, ofReal_one, add_im, mul_im, add_zero]
  ring_nf
  rw[←sub_eq_zero] at h₁ h₂
  simp only at h₁ h₂
  ring_nf at h₁ h₂
  calc _ = ↑j * ↑l₂.z₁.re - ↑j * ↑l₂.z₂.re + (↑l₂.z₂.re - ↑i * ↑l₁.z₁.re) + ↑i * ↑l₁.z₂.re - ↑l₁.z₂.re + (↑j * ↑l₂.z₁.im * I - ↑j * ↑l₂.z₂.im * I)  - ↑i * ↑l₁.z₁.im * I + ↑i * ↑l₁.z₂.im * I + ↑l₂.z₂.im * I - ↑l₁.z₂.im * I := by ring_nf
   _ = - (↑i * ↑l₁.z₁.re - ↑i * ↑l₁.z₂.re + ↑l₁.z₂.re + ↑j * ↑l₂.z₂.re + (-(↑j * ↑l₂.z₁.re) - ↑l₂.z₂.re) + ↑i * I * ↑l₁.z₁.im - ↑i * I * ↑l₁.z₂.im + (↑j * I * ↑l₂.z₂.im - ↑j * I * ↑l₂.z₁.im) + (I * ↑l₁.z₂.im - I * ↑l₂.z₂.im)) := by ring_nf
   _ = 0 := by rw[h₁, zero_add, h₂, neg_zero]

--(Nempty: l.points ∩ g.points ≠ ∅) (hl: l.z₁ ≠ l.z₂)
-- lemma ilc_L (l: line) (g: Construction.circle) (hg: 0 ≤ g.r): z ∈ l.points ∩ g.points ↔
--     let a := (l.z₁.re - l.z₂.re)^2 - (I*l.z₁.im - I*l.z₂.im)^2
--     let b := 2*((l.z₁.re - l.z₂.re) * (l.z₂.re - g.c.re) - (I*l.z₁.im - I*l.z₂.im) * (I*l.z₂.im-I*g.c.im))
--     let c := (l.z₂.re - g.c.re)^2 - (I*l.z₂.im - I*g.c.im)^2 - g.r^2
--     ∃ ι:ℝ, ι^2 * a + ι * b + c = 0  ∧ ι * l.z₁ + (1- ι) * l.z₂ = z := by
--   refine ⟨?_, ?_⟩ <;> intro h <;> simp only [line.points, circle.points, Set.mem_inter_iff,
--     Set.mem_setOf_eq, mem_sphere_iff_norm, norm_eq_abs] at h ⊢
--   . obtain ⟨⟨t ,h₁⟩, h₂⟩ := h
--     refine ⟨t, ?_, h₁⟩
--     rw[←sq_eq_sq (AbsoluteValue.nonneg _ _) hg, Complex.sq_abs, normSq_apply, ←h₁, ←sub_eq_zero] at h₂
--     simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, one_re, sub_im,
--       one_im, sub_self, add_im, mul_im, add_zero] at h₂
--     simp_rw [←mul_sub I, mul_pow,←mul_assoc, mul_comm _ I, ←mul_assoc, ←pow_two I, I_sq, neg_one_mul, neg_mul, sub_neg_eq_add]
--     norm_cast
--     rw[←h₂]
--     ring_nf
--   . obtain ⟨ι, h₁, h₂⟩ := h
--     refine ⟨⟨ι, h₂⟩, ?_⟩
--     rw[←sq_eq_sq (AbsoluteValue.nonneg _ _) hg, Complex.sq_abs, normSq_apply, ←h₂, ←sub_eq_zero]
--     simp_rw [←mul_sub I, mul_pow,←mul_assoc, mul_comm _ I, ←mul_assoc, ←pow_two I, I_sq, neg_one_mul, neg_mul, sub_neg_eq_add] at h₁
--     simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, one_re, sub_im, one_im, sub_self, add_im, mul_im, add_zero]
--     norm_cast at h₁
--     rw[←h₁]
--     ring_nf

lemma ilc_L  (c: Construction.circle) (l: line) (hc: 0 ≤ c.r): z ∈ c.points ∩ l.points ↔
    let a := (l.z₁.re - l.z₂.re)^2 - (I*l.z₁.im - I*l.z₂.im)^2
    let b := 2*((l.z₁.re - l.z₂.re) * (l.z₂.re - c.c.re) - (I*l.z₁.im - I*l.z₂.im) * (I*l.z₂.im-I*c.c.im))
    let c := (l.z₂.re - c.c.re)^2 - (I*l.z₂.im - I*c.c.im)^2 - c.r^2
    ∃ ι:ℝ, ι^2 * a + ι * b + c = 0  ∧ ι * l.z₁ + (1- ι) * l.z₂ = z := by
  refine ⟨?_, ?_⟩ <;> intro h <;> simp only [line.points, circle.points, Set.mem_inter_iff,
    Set.mem_setOf_eq, mem_sphere_iff_norm, norm_eq_abs] at h ⊢
  . obtain ⟨ h₁, ⟨t ,h₂⟩⟩ := h
    refine ⟨t, ?_, h₂⟩
    rw[←sq_eq_sq (AbsoluteValue.nonneg _ _) hc, Complex.sq_abs, normSq_apply, ←h₂, ←sub_eq_zero] at h₁
    simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, one_re, sub_im,
      one_im, sub_self, add_im, mul_im, add_zero] at h₁
    simp_rw [←mul_sub I, mul_pow,←mul_assoc, mul_comm _ I, ←mul_assoc, ←pow_two I, I_sq, neg_one_mul, neg_mul, sub_neg_eq_add]
    norm_cast
    rw[←h₁]
    ring_nf
  . obtain ⟨ι, h₁, h₂⟩ := h
    refine ⟨?_, ⟨ι, h₂⟩⟩
    rw[←sq_eq_sq (AbsoluteValue.nonneg _ _) hc, Complex.sq_abs, normSq_apply, ←h₂, ←sub_eq_zero]
    simp_rw [←mul_sub I, mul_pow,←mul_assoc, mul_comm _ I, ←mul_assoc, ←pow_two I, I_sq, neg_one_mul, neg_mul, sub_neg_eq_add] at h₁
    simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, one_re, sub_im, one_im, sub_self, add_im, mul_im, add_zero]
    norm_cast at h₁
    rw[←h₁]
    ring_nf

end Intersection

variable (L : Subfield ℂ) [ConjClosed L]

lemma ir_L (z : ℂ) (h : z ∈ L): ↑z.re ∈ L := by
  have :  z.re = (1/2:ℝ)  * (z + conj z) := by
    rw [Complex.add_conj]
    simp only [one_div, Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.ofReal_mul,
      isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_left]
  rw[this]
  apply mul_mem
  push_cast
  apply div_mem
  exact Subfield.one_mem L
  exact ofNat_mem L 2
  apply add_mem
  exact h
  exact conj_L L z h


lemma im_L (z : ℂ) (h : z ∈ L): z.im * Complex.I ∈ L := by
  have : z.im * Complex.I = z - z.re := by
    nth_rw 2 [←Complex.re_add_im z]
    ring
  rw[this]
  apply sub_mem
  exact h
  exact ir_L L z h


lemma distSq_L (z₁ z₂ : ℂ) (h₁ : z₁ ∈ L) (h₂ : z₂ ∈ L): ↑(Complex.normSq (z₁ - z₂)) ∈ L := by
  rw [Complex.normSq_apply]
  push_cast
  apply add_mem
  exact mul_mem (ir_L L (z₁ - z₂) (sub_mem h₁ h₂)) (ir_L L (z₁ - z₂) (sub_mem h₁ h₂))
  have : (z₁ - z₂).im * (z₁ - z₂).im = - (↑(z₁ - z₂).im * Complex.I * ( ↑(z₁ - z₂).im * Complex.I)) := by
    ring_nf
    simp only [Complex.I_sq, Complex.sub_im, Complex.ofReal_sub, mul_neg, mul_one, neg_neg]
  rw[this]
  apply neg_mem (mul_mem (im_L L (z₁ - z₂) (sub_mem h₁ h₂)) (im_L L (z₁ - z₂) (sub_mem h₁ h₂)))


lemma ill_L' (z : ℂ) (h : z ∈ ill L): z ∈ L := by
  simp only [ill, ne_eq, Set.mem_setOf_eq] at h
  obtain ⟨l₁, hl₁, l₂, hl₂, h, ne⟩ := h
  have zl₁i₂: z ∈ l₁.points ∩ l₂.points := h
  rw [ill_L] at h
  obtain ⟨i, j, hre, him, h⟩ := h
  rw [←h]
  have hz₁: l₁.z₁ ∈ L := by
    unfold Construction.L at hl₁
    simp at hl₁
    obtain ⟨z₁, _, hl₁, hz₁, _⟩ := hl₁
    simp_all only
  have hz₂: l₁.z₂ ∈ L := by
    unfold Construction.L at hl₁
    simp at hl₁
    obtain ⟨z₁, _, hl₁, _, hz₂⟩ := hl₁
    simp_all only
  have hz₃ : l₂.z₁ ∈ L := by
    unfold Construction.L at hl₂
    simp at hl₂
    obtain ⟨z₁, _, h₂, hz₃, _⟩ := hl₂
    simp_all only
  have hz₄ : l₂.z₂ ∈ L := by
    unfold Construction.L at hl₂
    simp at hl₂
    obtain ⟨z₁, _, h₂, _, hz₄⟩ := hl₂
    simp_all only
  suffices ↑i ∈ L by aesop
  by_cases h: (l₂.z₂.im * Complex.I - l₂.z₁.im * Complex.I) = 0
  . have div: (l₁.z₁.im - l₁.z₂.im:ℂ) ≠  (0:ℂ) :=  by
      obtain ⟨_, _, _, _, _ , _⟩ := hl₁
      obtain ⟨_, _, _, _, _ , _⟩ := hl₂
      by_contra h'
      have: parallel' l₁ l₂ := by
        norm_cast at h'
        have: l₂.z₁.im  - l₂.z₂.im  = 0 := by
          rw [sub_eq_zero, mul_eq_mul_right_iff] at h
          simp_all only [SetLike.mem_coe, ne_eq,Complex.ofReal_inj, Complex.I_ne_zero, or_false, sub_self, mul_zero, add_zero, Set.mem_inter_iff]
        apply @parallel'_if_im_eq l₁ l₂ ?_ _ h' this
        simp_all only [SetLike.mem_coe, ne_eq, Set.mem_inter_iff, not_false_eq_true]
        simp_all only [SetLike.mem_coe, ne_eq, Set.mem_inter_iff, not_false_eq_true]
      have: l₁.points = l₂.points := by
        apply @eq_of_parallel l₁ l₂ ?_ this (Exists.intro z zl₁i₂)
        simp_all only [SetLike.mem_coe, ne_eq, Set.mem_inter_iff, not_false_eq_true]
      contradiction -- Contradication to l₁.points ≠ l₂.points
    simp_rw [mul_comm Complex.I, h, mul_zero, add_zero] at him
    have: l₁.z₁.im * Complex.I  -  l₁.z₂.im * Complex.I  ≠ 0 := by
      simp_rw [← mul_comm Complex.I]
      rw[← mul_sub, mul_ne_zero_iff]
      refine ⟨Complex.I_ne_zero, div⟩
    rw[←eq_div_iff_mul_eq this] at him
    --simp_rw [mul_comm Complex.I] at him
    --rw[←mul_assoc, mul_comm ↑i Complex.I,mul_assoc, @mul_left_inj_of_invertible  _ _ _ _ (Complex.I) (invertibleOfNonzero Complex.I_ne_zero), ←eq_div_iff_mul_eq h'] at him
    rw[him]
    refine Subfield.div_mem L ?_ ?_
    exact Subfield.sub_mem L (im_L L l₂.z₂ hz₄) (im_L L l₁.z₂ hz₂)
    exact Subfield.sub_mem L (im_L L l₁.z₁ hz₁) (im_L L l₁.z₂ hz₂)
  . have him: (j:ℂ) = (l₂.z₂.im * Complex.I - l₁.z₂.im * Complex.I - i*l₁.z₁.im * Complex.I+ i*l₁.z₂.im * Complex.I) / (l₂.z₂.im * Complex.I -l₂.z₁.im * Complex.I) := by
      rw[propext (eq_div_iff_mul_eq h)]
      simp_rw[mul_sub,  ←mul_assoc]
      symm
      rw[sub_add, sub_eq_iff_eq_add, add_comm]
      simp_rw[ mul_comm _ Complex.I, ←mul_assoc,]
      simp_rw[mul_sub, ←mul_assoc, mul_comm _ Complex.I] at him
      rw[him]
    have div: ((l₂.z₂.im * Complex.I - l₂.z₁.im * Complex.I) * (l₁.z₁.re - l₁.z₂.re) - (l₁.z₁.im * Complex.I - l₁.z₂.im * Complex.I) * (l₂.z₂.re - l₂.z₁.re)) ≠  (0:ℂ) :=  by
      obtain ⟨_, _, _, _, _ , ne⟩ := hl₁
      by_contra h'
      have: parallel' l₁ l₂ := by
        obtain ⟨_, _, _, _, _ , _⟩ := hl₂
        apply @parallel'_if_im_eq' l₁ l₂ ?_ _ h'
        simp_all only [SetLike.mem_coe, ne_eq, Set.mem_inter_iff, not_false_eq_true]
        simp_all only [SetLike.mem_coe, ne_eq, Set.mem_inter_iff, not_false_eq_true]
      have: l₁.points = l₂.points := by
        apply @eq_of_parallel l₁ l₂ ?_ this (Exists.intro z zl₁i₂)
        simp_all only [SetLike.mem_coe, ne_eq, Set.mem_inter_iff, not_false_eq_true]
      contradiction -- Contradication to l₁.points ≠ l₂.points
    have hre: (i:ℂ) =  ((l₂.z₂.re - l₁.z₂.re) * (l₂.z₂.im * Complex.I - l₂.z₁.im * Complex.I) - (l₂.z₂.im * Complex.I - l₁.z₂.im * Complex.I) * (l₂.z₂.re - l₂.z₁.re)) / ((l₂.z₂.im * Complex.I - l₂.z₁.im * Complex.I) * (l₁.z₁.re - l₁.z₂.re) - (l₁.z₁.im * Complex.I - l₁.z₂.im * Complex.I) * (l₂.z₂.re - l₂.z₁.re))  := by
      rw[propext (eq_div_iff_mul_eq div)]
      symm
      rw[sub_eq_iff_eq_add, ←eq_div_iff_mul_eq h]
      suffices l₂.z₂.re - ↑l₁.z₂.re = i * (l₁.z₁.re - l₁.z₂.re) + (↑l₂.z₂.im * Complex.I - ↑l₁.z₂.im * Complex.I - ↑i * ↑l₁.z₁.im * Complex.I + ↑i * ↑l₁.z₂.im * Complex.I) / (↑l₂.z₂.im * Complex.I - ↑l₂.z₁.im * Complex.I) * (l₂.z₂.re - l₂.z₁.re) by {
        calc _ = ↑i * (↑l₁.z₁.re - ↑l₁.z₂.re) + (↑l₂.z₂.im * Complex.I - ↑l₁.z₂.im * Complex.I - ↑i * ↑l₁.z₁.im * Complex.I + ↑i * ↑l₁.z₂.im * Complex.I) / (↑l₂.z₂.im * Complex.I - ↑l₂.z₁.im * Complex.I) * (↑l₂.z₂.re - ↑l₂.z₁.re) := by exact this
          _ = ↑i * (↑l₁.z₁.re - ↑l₁.z₂.re) * ((↑l₂.z₂.im * Complex.I - ↑l₂.z₁.im * Complex.I) / (↑l₂.z₂.im * Complex.I - ↑l₂.z₁.im * Complex.I)) + (↑l₂.z₂.im * Complex.I - ↑l₁.z₂.im * Complex.I - ↑i * ↑l₁.z₁.im * Complex.I + ↑i * ↑l₁.z₂.im * Complex.I) / (↑l₂.z₂.im * Complex.I - ↑l₂.z₁.im * Complex.I) * (↑l₂.z₂.re - ↑l₂.z₁.re)  := by rw[div_self h, mul_one]
          _ = (↑i * ((↑l₂.z₂.im * Complex.I - ↑l₂.z₁.im * Complex.I) * (↑l₁.z₁.re - ↑l₁.z₂.re) - (↑l₁.z₁.im * Complex.I - ↑l₁.z₂.im * Complex.I) * (↑l₂.z₂.re - ↑l₂.z₁.re)) + (↑l₂.z₂.im * Complex.I - ↑l₁.z₂.im * Complex.I) * (↑l₂.z₂.re - ↑l₂.z₁.re)) / (↑l₂.z₂.im * Complex.I - ↑l₂.z₁.im * Complex.I) := by ring_nf
        }
      rw[←him]
      symm
      exact hre
    rw[hre]
    refine Subfield.div_mem L ?_ ?_
    . refine Subfield.sub_mem L ?_ ?_
      . refine Subfield.mul_mem L ?_ ?_
        exact Subfield.sub_mem L (ir_L L l₂.z₂ hz₄) (ir_L L l₁.z₂ hz₂)
        exact Subfield.sub_mem L (im_L L l₂.z₂ hz₄) (im_L L l₂.z₁ hz₃)
      . refine Subfield.mul_mem L ?_ ?_
        exact Subfield.sub_mem L (im_L L l₂.z₂ hz₄) (im_L L l₁.z₂ hz₂)
        exact Subfield.sub_mem L (ir_L L l₂.z₂ hz₄) (ir_L L l₂.z₁ hz₃)
    . refine Subfield.sub_mem L ?_ ?_
      . refine Subfield.mul_mem L ?_ ?_
        exact Subfield.sub_mem L (im_L L l₂.z₂ hz₄) (im_L L l₂.z₁ hz₃)
        exact Subfield.sub_mem L (ir_L L l₁.z₁ hz₁) (ir_L L l₁.z₂ hz₂)
      . refine Subfield.mul_mem L ?_ ?_
        exact Subfield.sub_mem L (im_L L l₁.z₁ hz₁) (im_L L l₁.z₂ hz₂)
        exact Subfield.sub_mem L (ir_L L l₂.z₂ hz₄) (ir_L L l₂.z₁ hz₃)


-- alter beweis
  -- simp only [ill, Set.mem_inter_iff, ne_eq, Set.mem_setOf_eq] at h
  -- obtain ⟨l₁, hl₁, l₂, h₂, ⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hl⟩ := h
  -- have hz₁: l₁.z₁ ∈ L := by
  --   unfold Construction.L at hl₁
  --   simp at hl₁
  --   obtain ⟨z₁, _, hl₁, hz₁, _⟩ := hl₁
  --   simp_all only
  -- have hz₂: l₁.z₂ ∈ L := by
  --   unfold Construction.L at hl₁
  --   simp at hl₁
  --   obtain ⟨z₁, _, hl₁, _, hz₂⟩ := hl₁
  --   simp_all only
  -- have hz₃ : l₂.z₁ ∈ L := by
  --   unfold Construction.L at h₂
  --   simp at h₂
  --   obtain ⟨z₁, _, h₂, hz₃, _⟩ := h₂
  --   simp_all only
  -- have hz₄ : l₂.z₂ ∈ L := by
  --   unfold Construction.L at h₂
  --   simp at h₂
  --   obtain ⟨z₁, _, h₂, _, hz₄⟩ := h₂
  --   simp_all only

  -- sorry

open IntermediateField Complex Polynomial
-- lemma ilc_L' (z : ℂ) (h : z ∈ ilc L): ∃ ω ∈ L, z ∈ L⟮ω^(1/2:ℂ)⟯ := by sorry
lemma sq_add_sq_eq_zero (a b :ℝ) : a^2 + b^2 = 0 ↔ a = 0 ∧ b = 0 := by
  refine ⟨?_, ?_⟩ <;> intro h
  . rw [add_eq_zero_iff_eq_neg] at h
    have _ : 0 ≤ a^2 ∧  0 ≤ b^2:= by
      refine ⟨pow_two_nonneg a, pow_two_nonneg b⟩
    have h : a^2 = 0 ∧ b^2 = 0:= by
      refine ⟨(by linarith) , (by linarith)⟩
    simp_rw [pow_eq_zero_iff (by exact Ne.symm (Nat.zero_ne_add_one 1))] at h
    exact h
  . simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]

lemma quadratic_formula (ι u v w : ℂ) (h:  u * ι ^ 2 +  v * ι + w = 0 ) (hu: u≠0): ι = - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ) ∨ ι = - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ):= by
    sorry

lemma ilc_L' (z : ℂ) (h : z ∈ ilc L): ∃ ω ∈ L, ∃ x : ℂ, x * x = ω ∧ z ∈ L⟮x⟯ := by
  obtain ⟨c, hc, l, hl, hz⟩ := h
  have: 0 ≤ c.r := by
    simp only [Construction.C, SetLike.mem_coe, ne_eq, Set.mem_setOf_eq] at hc
    obtain ⟨_, _, _, _, _⟩ := hc
    simp_all only [dist_nonneg]
  rw[ilc_L _ _ this] at hz
  obtain ⟨ι, ⟨hι, hz⟩⟩ := hz
  have hlz₁: l.z₁ ∈ L := by
    simp only [Construction.L, SetLike.mem_coe, ne_eq, Set.mem_setOf_eq] at hl
    obtain ⟨_, _, _, _, _⟩ := hl
    simp_all only
  have hlz₂: l.z₂ ∈ L := by
    simp only [Construction.L, SetLike.mem_coe, ne_eq, Set.mem_setOf_eq] at hl
    obtain ⟨_, _, _, _, _⟩ := hl
    simp_all only
  have hcc: c.c ∈ L := by
    simp only [Construction.C, SetLike.mem_coe, ne_eq, Set.mem_setOf_eq] at hc
    obtain ⟨_ , _, _, _, _⟩ := hc
    simp_all only
  have hcr: (c.r:ℂ)^2 ∈ L := by
    simp only [Construction.C, SetLike.mem_coe, ne_eq, Set.mem_setOf_eq] at hc
    obtain ⟨_, _, _, _, _⟩ := hc
    norm_cast
    simp_all only [dist_eq,Complex.sq_abs, distSq_L]
  let u := (l.z₁.re - l.z₂.re)^2 - (l.z₁.im*I - l.z₂.im*I)^2
  let v := 2*((l.z₁.re - l.z₂.re) * (l.z₂.re - c.c.re) - (l.z₁.im*I - l.z₂.im*I) * (l.z₂.im*I-c.c.im*I))
  let w := (l.z₂.re - c.c.re)^2 - (l.z₂.im*I - c.c.im*I)^2 - c.r^2
  have hu: u ∈ L := by
    refine sub_mem ?_ ?_
    . refine pow_mem ?_ 2
      exact sub_mem (ir_L L l.z₁ hlz₁) (ir_L L l.z₂ hlz₂)
    . refine pow_mem ?_ 2
      exact sub_mem (im_L L l.z₁ hlz₁) (im_L L l.z₂ hlz₂)
  have hv: v ∈ L := by
    refine mul_mem (ofNat_mem L 2) ?_
    . refine sub_mem ?_ ?_
      . refine mul_mem ?_ ?_
        exact sub_mem (ir_L L l.z₁ hlz₁) (ir_L L l.z₂ hlz₂)
        exact sub_mem (ir_L L l.z₂ hlz₂) (ir_L L c.c hcc)
      . refine mul_mem ?_ ?_
        exact sub_mem (im_L L l.z₁ hlz₁) (im_L L l.z₂ hlz₂)
        exact sub_mem (im_L L l.z₂ hlz₂) (im_L L c.c hcc)
  have hw: w ∈ L := by
    refine sub_mem ?_ ?_
    . refine sub_mem ?_ ?_
      . refine pow_mem ?_ 2
        exact sub_mem (ir_L L l.z₂ hlz₂) (ir_L L c.c hcc)
      . refine pow_mem ?_ 2
        exact sub_mem (im_L L l.z₂ hlz₂) (im_L L c.c hcc)
    . exact hcr
  use (v^2 / (4 * u^2) - w / u)
  refine ⟨?_, ⟨(v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ), ?_, ?_⟩⟩
  . refine sub_mem ?_ ?_
    . refine div_mem ?_ ?_
      exact pow_mem hv 2
      exact mul_mem (ofNat_mem L 4) (pow_mem hu 2)
    . exact div_mem hw hu
  . rw[←pow_two, ← cpow_nat_mul, one_div,]
    norm_cast
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀, cpow_one]
  . have cast_L {x : ℂ}(h: x ∈ L): x ∈ (↥L)⟮(v ^ 2 / (4 * u ^ 2) - w / u) ^ (1 / 2:ℂ)⟯ := by
      unfold IntermediateField.adjoin
      apply Subfield.subset_closure
      apply Or.inl
      simp only [Set.mem_range, Subtype.exists]
      refine ⟨x, h, rfl⟩
    rw [←hz]
    suffices (ι:ℂ) ∈ (↑L )⟮(v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ)⟯ by{
      refine add_mem (mul_mem this (cast_L hlz₁)) (mul_mem ?_ (cast_L hlz₂))
      exact sub_mem (by apply OneMemClass.one_mem) this
    }
    have: u ≠ 0 := by
      simp only [← sub_mul, mul_pow, I_sq, mul_neg, mul_one, sub_neg_eq_add, ne_eq, u]
      norm_cast
      rw [sq_add_sq_eq_zero, sub_eq_zero, sub_eq_zero, ← Complex.ext_iff]
      obtain ⟨_,_,_,_,_,_⟩ := hl
      simp_all only [one_div, SetLike.mem_coe, ne_eq, not_false_eq_true]
    have h: ι = - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ) ∨ ι = - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ) := by
      have hι:  u * ι ^ 2 +  v * ι + w = 0 := by rw[←hι]; ring
      exact quadratic_formula ι u v w hι this
    cases h <;> rename_i h <;> rw[h]
    exact add_mem (div_mem (neg_mem (cast_L hv)) (mul_mem (ofNat_mem _ 2) (cast_L hu))) (IntermediateField.mem_adjoin_simple_self _ _)
    exact sub_mem (div_mem (neg_mem (cast_L hv)) (mul_mem (ofNat_mem _ 2) (cast_L hu))) (IntermediateField.mem_adjoin_simple_self _ _)


-- lemma icc_L' (z : ℂ) (h : z ∈ icc L): ∃ ω ∈ L, z ∈ L⟮ω^(1/2:ℂ)⟯ := by sorry

lemma icc_L (z : ℂ) (h : z ∈ icc L): ∃ ω ∈ L,∃ x : ℂ, x * x = ω ∧ z ∈ L⟮x⟯ := by sorry

end ConjClosed

example ( a b c :ℂ) (h: c ≠ 0): a * c = b ↔ a = b * c⁻¹ := by
  refine ⟨?_, ?_⟩ <;> intros h'
  . rw [CancelDenoms.inv_subst h h']
  . exact (eq_mul_inv_iff_mul_eq₀ h).mp h'
