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
    refine ⟨(a+I*b-I), I*b, (by simp only), ?_, ir_M_inf _ h₀ h₁ _ hb, ?_⟩
    . simp only [sub_M_Inf, add_M_Inf, ir_M_inf M h₀ h₁ b hb, imath_M_inf, h₀, h₁, ha]
    simp [ext_iff]
  have hlr : lr ∈ L (M_inf M) := by
    refine ⟨1, 0, (by simp only), M_M_inf M h₁,  M_M_inf M h₀, ?_⟩
    simp only [ne_eq, one_ne_zero, not_false_eq_true]
  refine ill_M_inf M ⟨l,hl, lr, hlr,  ⟨b, ?_⟩, ⟨a*b, ?_⟩⟩
  push_cast; ring_nf
  push_cast; ring_nf


lemma real_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ) (h: z ∈ M_inf M): ↑z.re ∈ M_inf M := sorry

lemma im_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ) (h: z ∈ M_inf M): ↑z.im ∈ M_inf M := sorry

lemma z_iff_re_im_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ): z ∈ M_inf M ↔
    ↑z.re ∈ M_inf M ∧ ↑z.im ∈ M_inf M := sorry

lemma mul_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a b :ℂ ) (ha: a ∈ M_inf M) (hb: b ∈ M_inf M): a * b ∈ M_inf M:= by
  refine (z_iff_re_im_M_inf M h₀ h₁ (a * b)).mpr ⟨?_, ?_⟩ <;>
  simp only [mul_re, mul_im, ofReal_sub, ofReal_add]
  . apply sub_M_Inf M h₀
    exact ab_in_M_inf M h₀ h₁ _ _ (real_in_M_inf M h₀ h₁ a ha) (real_in_M_inf M h₀ h₁ b hb)
    exact ab_in_M_inf M h₀ h₁ _ _ (im_in_M_inf M h₀ h₁ a ha) (im_in_M_inf M h₀ h₁ b hb)
  . apply add_M_Inf M h₀
    exact ab_in_M_inf M h₀ h₁ _ _ (real_in_M_inf M h₀ h₁ a ha) (im_in_M_inf M h₀ h₁ b hb)
    exact ab_in_M_inf M h₀ h₁ _ _ (im_in_M_inf M h₀ h₁ a ha) (real_in_M_inf M h₀ h₁ b hb)
