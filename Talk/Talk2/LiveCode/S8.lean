import Construction.Chapter1.set_MInf

open Construction Complex

lemma add_M_Inf (M: Set ℂ) (h₀: (0:ℂ)∈ M) (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ (M_inf M)) (hz₂ : z₂ ∈ (M_inf M)):
     z₁ + z₂ ∈ (M_inf M) := sorry

lemma sub_M_Inf (M: Set ℂ) (h₀: (0:ℂ)∈ M) (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ (M_inf M)) (hz₂ : z₂ ∈ (M_inf M)):
     z₁ - z₂ ∈ (M_inf M) := sorry

lemma imath_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M): Complex.I ∈ M_inf M := sorry

lemma mul_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a b :ℂ ) (ha: a ∈ M_inf M) (hb: b ∈ M_inf M): a * b ∈ M_inf M:= sorry

lemma real_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ) (h: z ∈ M_inf M): ↑z.re ∈ M_inf M := sorry

lemma im_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ) (h: z ∈ M_inf M): ↑z.im ∈ M_inf M := sorry


lemma ainv_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a :ℝ) (ha: ↑a ∈ M_inf M): ↑(a⁻¹) ∈ M_inf M := by
  by_cases h: a = 0
  . simp [h]
    exact M_M_inf _ h₀
  let l: line := {z₁ := 1-I*a+I, z₂ := I}
  let lr : line := {z₁ := 1, z₂ := 0}
  have hl : l ∈ L (M_inf M) := by
    refine ⟨(1-I*a+I), I, (by simp only), ?_, imath_M_inf M h₀ h₁, ?_⟩
    . apply add_M_Inf M h₀ (1-I*a) I ?_ (imath_M_inf M h₀ h₁)
      exact sub_M_Inf M h₀ 1 (I*a) (M_M_inf M h₁) (mul_M_inf M h₀ h₁ _ _ (imath_M_inf M h₀ h₁) ha)
    simp [ext_iff]
  have hlr : lr ∈ L (M_inf M) := by
    refine ⟨1, 0, (by simp only), M_M_inf M h₁, M_M_inf M h₀, ?_⟩
    simp
  refine ill_M_inf M ⟨l, hl, lr, hlr, ⟨a⁻¹, ?_⟩ , ⟨a⁻¹, ?_⟩⟩
  . ring_nf
    simp [h, mul_rotate]
  simp only [ofReal_inv, mul_one, mul_zero, add_zero]

-- Helper lemma for the next lemma
lemma z_inv_eq (z:ℂ) (hz: z ≠ 0): z⁻¹ = z.re / (z.re^2+z.im^2)-(z.im/ (z.re^2+z.im^2) )*I := sorry

lemma inv_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a :ℂ ) (ha: a ∈ M_inf M): a⁻¹ ∈ M_inf M:= by
  by_cases h: a = 0
  . simp only [h, inv_zero]
    exact M_M_inf _ h₀
  simp_rw [z_inv_eq _ h, Field.div_eq_mul_inv, pow_two]
  apply sub_M_Inf M h₀
  . apply mul_M_inf M h₀ h₁ _ _ (real_in_M_inf M h₀ h₁ a ha)
    norm_cast
    apply ainv_in_M_inf M h₀ h₁
    push_cast
    apply add_M_Inf M h₀
    exact mul_M_inf M h₀ h₁ _ _ (real_in_M_inf M h₀ h₁ _ ha) (real_in_M_inf M h₀ h₁ _ ha)
    exact mul_M_inf M h₀ h₁ _ _ (im_in_M_inf M h₀ h₁ _ ha) (im_in_M_inf M h₀ h₁ _ ha)
  . apply mul_M_inf M h₀ h₁ _ _ ?_ (imath_M_inf M h₀ h₁)
    apply mul_M_inf M h₀ h₁ _ _ (im_in_M_inf M h₀ h₁ _ ha)
    norm_cast
    apply ainv_in_M_inf M h₀ h₁
    push_cast
    apply add_M_Inf M h₀
    exact mul_M_inf M h₀ h₁ _ _ (real_in_M_inf M h₀ h₁ _ ha) (real_in_M_inf M h₀ h₁ _ ha)
    exact mul_M_inf M h₀ h₁ _ _ (im_in_M_inf M h₀ h₁ _ ha) (im_in_M_inf M h₀ h₁ _ ha)
