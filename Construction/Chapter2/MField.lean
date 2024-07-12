import Construction.Chapter1.basic_construction

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
    push_cast
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

def conj_set (M : Set ℂ) : Set ℂ := {starRingEnd ℂ z | z ∈ M}

lemma conj_conj_id (M : Set ℂ) : conj_set (conj_set M) = M := by
  simp only [Set.mem_setOf_eq, exists_exists_and_eq_and, RingHomCompTriple.comp_apply,
    RingHom.id_apply, exists_eq_right, Set.setOf_mem_eq, conj_set]

class ConjClosed (M : Set ℂ) : Prop where
  equal: M = conj_set M

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
