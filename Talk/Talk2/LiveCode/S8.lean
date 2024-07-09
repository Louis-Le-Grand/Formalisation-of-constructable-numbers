import Construction.Chapter1.set_MInf

open Construction Complex

lemma add_M_Inf (M: Set ℂ) (h₀: (0:ℂ)∈ M) (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ (M_inf M)) (hz₂ : z₂ ∈ (M_inf M)):
     z₁ + z₂ ∈ (M_inf M) := sorry

lemma sub_M_Inf (M: Set ℂ) (h₀: (0:ℂ)∈ M) (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ (M_inf M)) (hz₂ : z₂ ∈ (M_inf M)):
     z₁ - z₂ ∈ (M_inf M) := sorry

lemma imath_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M): Complex.I ∈ M_inf M := sorry

lemma ir_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (r : ℝ) (hr : ↑r ∈ (M_inf M)):
    Complex.I * r ∈ (M_inf M) := sorry

lemma mul_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a b :ℂ ) (ha: a ∈ M_inf M) (hb: b ∈ M_inf M): a * b ∈ M_inf M:= sorry

lemma real_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ) (h: z ∈ M_inf M): ↑z.re ∈ M_inf M := sorry

lemma im_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ) (h: z ∈ M_inf M): ↑z.im ∈ M_inf M := sorry


lemma ainv_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a :ℝ) (ha: ↑a ∈ M_inf M): ↑(a⁻¹) ∈ M_inf M := by
  by_cases h: a = 0
  . simp [h]
    exact M_M_inf _ h₀
  rw[←ne_eq] at h
  let l: line := {z₁ := 1-I*a+I, z₂ := I}
  let lr : line := {z₁ := 1, z₂ := 0}
  have hl : l ∈ L (M_inf M) := by
    use (1-I*a+I), I
    refine ⟨(by simp only), ?_, (by exact imath_M_inf M h₀ h₁), ?_⟩
    . apply add_M_Inf M h₀ (1-I*a) I
      apply sub_M_Inf M h₀ 1 (I*a)
      exact M_M_inf M h₁
      exact ir_M_inf M h₀ h₁ a ha
      exact imath_M_inf M h₀ h₁
    simp [ext_iff]
  have hlr : lr ∈ L (M_inf M) := by
    use 1, 0
    refine ⟨(by simp only), (by exact M_M_inf M h₁), (by exact M_M_inf M h₀), ?_⟩
    simp
  apply ill_M_inf M
  refine ⟨l, (by exact hl), lr, (by exact hlr), ?_, ?_⟩
  . use a⁻¹
    ring_nf
    rw [mul_rotate]
    simp [*]
  use a⁻¹
  simp only [ofReal_inv, mul_one, mul_zero, add_zero]

-- Helper lemma for the next lemma
lemma z_inv_eq (z:ℂ) (hz: z ≠ 0): z⁻¹ = z.re / (z.re^2+z.im^2)-(z.im/ (z.re^2+z.im^2) )*I := sorry

lemma inv_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a :ℂ ) (ha: a ∈ M_inf M): a⁻¹ ∈ M_inf M:= by
  by_cases h: a = 0
  . simp [h]
    exact M_M_inf _ h₀
  rw[←ne_eq] at h
  rw[z_inv_eq _ h]
  refine sub_M_Inf M h₀ (↑a.re / (↑a.re ^ 2 + ↑a.im ^ 2)) (↑a.im / (↑a.re ^ 2 + ↑a.im ^ 2) * I) ?_ ?_
  rw[ Field.div_eq_mul_inv]
  apply mul_M_inf M h₀ h₁ (↑a.re) (↑a.re ^ 2 + ↑a.im ^ 2)⁻¹ ?_ ?_
  exact real_in_M_inf M h₀ h₁ a ha
  norm_cast
  apply ainv_in_M_inf M h₀ h₁
  push_cast
  apply add_M_Inf M h₀ (↑a.re ^ 2) (↑a.im ^ 2)
  rw[pow_two]
  apply mul_M_inf M h₀ h₁ (↑a.re) (↑a.re) (by apply real_in_M_inf M h₀ h₁; exact ha)
    (by apply real_in_M_inf M h₀ h₁; exact ha)
  rw[pow_two]
  apply mul_M_inf M h₀ h₁ (↑a.im) (↑a.im) (by apply im_in_M_inf M h₀ h₁; exact ha)
    (by apply im_in_M_inf M h₀ h₁; exact ha)
  apply mul_M_inf M h₀ h₁ _ _ ?_ (by exact imath_M_inf M h₀ h₁)
  rw[ Field.div_eq_mul_inv]
  apply mul_M_inf M h₀ h₁ _ _ (by exact im_in_M_inf M h₀ h₁ a ha)
  norm_cast
  apply ainv_in_M_inf M h₀ h₁
  push_cast
  apply add_M_Inf M h₀ (↑a.re ^ 2) (↑a.im ^ 2)
  rw[pow_two]
  apply mul_M_inf M h₀ h₁ (↑a.re) (↑a.re) (by apply real_in_M_inf M h₀ h₁; exact ha)
    (by apply real_in_M_inf M h₀ h₁; exact ha)
  rw[pow_two]
  apply mul_M_inf M h₀ h₁ (↑a.im) (↑a.im) (by apply im_in_M_inf M h₀ h₁; exact ha)
    (by apply im_in_M_inf M h₀ h₁; exact ha)
