import Construction.Chapter1.set_MInf

open Construction Complex

lemma add_M_Inf (M: Set ℂ) (h₀: (0:ℂ)∈ M) (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ (M_inf M)) (hz₂ : z₂ ∈ (M_inf M)):
     z₁ + z₂ ∈ (M_inf M) := sorry

lemma sub_M_Inf (M: Set ℂ) (h₀: (0:ℂ)∈ M) (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ (M_inf M)) (hz₂ : z₂ ∈ (M_inf M)):
     z₁ - z₂ ∈ (M_inf M) := sorry

lemma imath_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M): Complex.I ∈ M_inf M := sorry

lemma ir_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (r : ℝ) (hr : ↑r ∈ (M_inf M)):
    Complex.I * r ∈ (M_inf M) := sorry

lemma ab_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a b :ℝ) (ha: ↑a ∈ M_inf M) (hb: ↑b ∈ M_inf M):
    ↑(a * b) ∈ M_inf M := by
  let l : line := {z₁ := a+I*b-I, z₂ := I*b}
  let lr : line := {z₁ := 1, z₂ := 0}
  have hl : l ∈ L (M_inf M) := by
    use (a+I*b-I), I*b
    refine ⟨(by simp only), ?_, (by exact ir_M_inf M h₀ h₁ b hb), ?_⟩
    simp only [sub_M_Inf M h₀ (a+I*b) I, add_M_Inf M h₀ a (I*b), ha, ir_M_inf M h₀ h₁ b hb, imath_M_inf M h₀ h₁]
    simp [ext_iff]
  have hlr : lr ∈ L (M_inf M) := by
    use 1, 0
    refine ⟨(by simp only), (by exact M_M_inf M h₁), (by exact M_M_inf M h₀), ?_⟩
    simp
  apply ill_M_inf M
  refine ⟨l, (by exact hl), lr, (by exact hlr), ?_, ?_⟩
  . use b
    push_cast
    ring_nf
  . use a*b
    push_cast
    ring_nf


lemma z_iff_re_im_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ): z ∈ M_inf M ↔
    ↑z.re ∈ M_inf M ∧ ↑z.im ∈ M_inf M := sorry

lemma real_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ) (h: z ∈ M_inf M): ↑z.re ∈ M_inf M := sorry

lemma im_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ) (h: z ∈ M_inf M): ↑z.im ∈ M_inf M := sorry


lemma mul_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a b :ℂ ) (ha: a ∈ M_inf M) (hb: b ∈ M_inf M): a * b ∈ M_inf M:= by
  refine (z_iff_re_im_M_inf M h₀ h₁ (a * b)).mpr ⟨?_, ?_⟩
  . simp only [mul_re, ofReal_sub, ofReal_mul]
    apply sub_M_Inf M h₀
    norm_cast
    apply ab_in_M_inf M h₀ h₁
    exact real_in_M_inf M h₀ h₁ a ha
    exact real_in_M_inf M h₀ h₁ b hb
    norm_cast
    apply ab_in_M_inf M h₀ h₁
    exact im_in_M_inf M h₀ h₁ a ha
    exact im_in_M_inf M h₀ h₁ b hb
  . simp only [mul_im, ofReal_add, ofReal_mul]
    apply add_M_Inf M h₀
    norm_cast
    apply ab_in_M_inf M h₀ h₁
    exact real_in_M_inf M h₀ h₁ a ha
    exact im_in_M_inf M h₀ h₁ b hb
    norm_cast
    apply ab_in_M_inf M h₀ h₁
    exact im_in_M_inf M h₀ h₁ a ha
    exact real_in_M_inf M h₀ h₁ b hb
