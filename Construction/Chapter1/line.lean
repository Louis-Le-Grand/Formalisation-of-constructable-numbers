import Construction.Chapter1.def
-- import Mathlib.Analysis.SpecialFunctions.Complex.Arg --! For section safekeeping

namespace Construction

lemma line_pionts_iff (l : line) (α: ℂ) (hα: α ∈ l.points) : l.points = {z | ∃ t:ℝ, α + t * (l.z₁ - l.z₂) = z} := by
  ext x
  simp only [line.points, Set.mem_setOf_eq] at hα ⊢
  obtain ⟨tα, htα⟩ := hα
  refine ⟨?_,?_⟩ <;> intro h <;> obtain ⟨t, ht⟩ := h
  . refine ⟨t - tα, ?_⟩
    rw [←htα]
    push_cast
    ring_nf  at ht ⊢
    exact ht
  . refine ⟨t + tα, ?_⟩
    push_cast
    ring_nf  at htα ht ⊢
    rw [add_sub, add_assoc, add_comm (l.z₁ * t), ←add_assoc, htα, ←add_sub, add_comm]
    exact ht

section parallel

def parallel (l₁ l₂ : line) := ∃ z, l₁.points = {x + z | x ∈ l₂.points}

--not in Blueprint
lemma parallel_self (l : line) : parallel l l := by
  use 0
  simp

--not in Blueprint
lemma parallel_symm (l₁ l₂ : line) : parallel l₁ l₂ → parallel l₂ l₁ := by
  intro h
  obtain ⟨z, hz⟩ := h
  use -z
  simp[hz]

lemma parallel_basis(l₁ l₂ : line) (h: l₁.z₁ - l₂.z₁ = l₁.z₂ - l₂.z₂ ): parallel l₁ l₂  := by
  unfold parallel
  use l₁.z₁ - l₂.z₁
  unfold line.points
  ext x
  simp
  constructor
  . intro hx
    obtain ⟨t, ht⟩ := hx
    simp only [←ht, sub_mul,←add_sub_assoc, one_mul]
    use t
    rw [←sub_eq_zero, ←sub_add, ←sub_sub]
    calc ↑t * l₂.z₁ + l₂.z₂ - ↑t * l₂.z₂ + l₁.z₁ - l₂.z₁ - ↑t * l₁.z₁ - l₁.z₂ + ↑t * l₁.z₂
     = t * l₂.z₁ - ↑t * l₂.z₂+ t * l₁.z₂ - ↑t * l₁.z₁  + l₁.z₁ - l₂.z₁  - l₁.z₂  + l₂.z₂:= by ring
      _ = t * (l₁.z₂ - l₂.z₂  - l₁.z₁ + l₂.z₁ ) - (l₁.z₂ - l₂.z₂ - l₁.z₁ + l₂.z₁) := by ring
      _ = t * (l₁.z₁ - l₂.z₁ - l₁.z₁ + l₂.z₁) - (l₁.z₁ - l₂.z₁ - l₁.z₁ + l₂.z₁) := by rw[←h]
      _ = 0 := by ring
  intro hx
  obtain ⟨a, ha⟩ := hx
  simp only [←ha, sub_mul,←add_sub_assoc, one_mul]
  use a
  rw [←sub_eq_zero, ←sub_add, ←sub_sub, ←sub_add, ←sub_sub]
  calc _ = ↑a * l₁.z₁ - ↑a * l₁.z₂ - ↑a * l₂.z₁ + ↑a * l₂.z₂ - l₁.z₁ + l₂.z₁ + l₁.z₂ - l₂.z₂ := by ring
    _ = a * (l₁.z₁ - l₂.z₁ - l₁.z₂ + l₂.z₂) + l₂.z₁ - l₁.z₁ + l₁.z₂ - l₂.z₂ := by ring
    _ = a * (l₁.z₂ - l₂.z₂- l₁.z₂ + l₂.z₂) + l₂.z₁ - l₁.z₁ + l₁.z₂ - l₂.z₂ := by rw [h]
    _ = 0 := by ring_nf; rw[←h]; ring

end parallel


section DirectionVectorsOfLines

variable (l : line)

def direction_vector: ℂ := l.z₁ - l.z₂

--not in Blueprint
lemma direction_vector_not_zero (hl: l.z₁ ≠ l.z₂): direction_vector l ≠ 0 := by
  unfold direction_vector
  rw [sub_ne_zero]
  exact hl

--not in Blueprint
lemma line_piont_iff: l.points = {x | ∃ t:ℝ, l.z₂ + t * direction_vector l = x} := by
  simp only [line.points, sub_mul, one_mul, add_sub, add_comm _ l.z₂, direction_vector, mul_sub]

end DirectionVectorsOfLines

section DirectionVectorsOfLines_parallel

variable (l₁ l₂ : line)

def parallel' : Prop := ∃ k:ℝ, direction_vector l₁ = k * direction_vector l₂

lemma parallel_iff_parallel' {hl₁_ne : l₁.z₁ ≠ l₁.z₂}: parallel' l₁ l₂ → parallel l₁ l₂ := by
  unfold parallel parallel' direction_vector line.points
  intro h
  obtain ⟨k, hk⟩ := h
  have: (k:ℂ) ≠ 0 := by
    by_contra h
    rw[h, zero_mul, sub_eq_zero] at hk
    contradiction
  use l₁.z₂ - l₂.z₂
  ext x
  refine ⟨?_,?_⟩ <;> intro h
  . obtain ⟨t, ht⟩ := h
    simp only [Set.mem_setOf_eq, exists_exists_eq_and]
    refine ⟨t*k,?_⟩
    ring_nf
    push_cast
    rw [←mul_sub,mul_assoc, ←hk, ←ht]
    ring_nf
  . simp only [Set.mem_setOf_eq, exists_exists_eq_and] at h ⊢
    obtain ⟨t, ht⟩ := h
    refine ⟨t/k,?_⟩
    ring_nf
    push_cast at hk ⊢
    rw[←@invOf_mul_eq_iff_eq_mul_left _ _ _ _ (k:ℂ) (invertibleOfNonzero this), invOf_eq_inv] at hk
    rw [←mul_sub, mul_assoc, hk, ←ht]
    ring_nf

--not in Blueprint for need in the proof of ilc_L'
lemma parallel'_if_im_eq {hl₂_ne : l₂.z₁ ≠ l₂.z₂} (hl₁: l₁.z₁.im - l₁.z₂.im = 0) (hl₂: l₂.z₁.im - l₂.z₂.im = 0): parallel' l₁ l₂ := by
  simp only [parallel', direction_vector, Complex.ext_iff, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, hl₂, mul_zero, sub_zero, hl₁,
    Complex.mul_im, zero_mul, add_zero, and_true]
  have: (l₂.z₁.re - l₂.z₂.re) ≠ 0 := by
    by_contra h
    rw [Ne.eq_def, Complex.ext_iff] at hl₂_ne
    rw [sub_eq_zero] at hl₂ h
    have: (l₂.z₁.re = l₂.z₂.re ∧ l₂.z₁.im = l₂.z₂.im) := ⟨h, hl₂⟩
    contradiction
  refine ⟨ (l₁.z₁.re - l₁.z₂.re) / (l₂.z₁.re - l₂.z₂.re), (div_mul_cancel₀ (l₁.z₁.re - l₁.z₂.re) this).symm⟩

--not in Blueprint for need in the proof of ilc_L'
lemma parallel'_if_im_eq' {hl₁_ne : l₁.z₁ ≠ l₁.z₂} {hl₂_ne : l₂.z₁ ≠ l₂.z₂} (h: ((l₂.z₂.im * Complex.I - l₂.z₁.im * Complex.I) * (l₁.z₁.re - l₁.z₂.re) - (l₁.z₁.im * Complex.I - l₁.z₂.im * Complex.I) * (l₂.z₂.re - l₂.z₁.re)) =  0): parallel' l₁ l₂ := by
  unfold parallel' direction_vector
  rw[←sub_mul, ←sub_mul,mul_comm _ Complex.I, mul_comm _ Complex.I, mul_assoc, mul_assoc, ←mul_sub Complex.I, mul_eq_zero, sub_eq_zero] at h
  simp only [Complex.I_ne_zero, false_or] at h
  norm_cast at h
  have h: (l₂.z₁.im - l₂.z₂.im) * (l₁.z₁.re - l₁.z₂.re) = (l₁.z₁.im - l₁.z₂.im) * (l₂.z₁.re - l₂.z₂.re) := by
    calc _ = -1 * ((l₂.z₂.im - l₂.z₁.im) * (l₁.z₁.re - l₁.z₂.re)) := by ring_nf
      _ = -1 * ((l₁.z₁.im - l₁.z₂.im) * (l₂.z₂.re - l₂.z₁.re)) := by rw [h]
      _ = _ := by ring_nf
  by_cases h₁: l₂.z₁.re - l₂.z₂.re = 0
  . simp only [h₁, mul_zero, mul_eq_zero] at h
    have: l₂.z₁.im - l₂.z₂.im ≠  0 := by{
      by_contra h
      simp only [ne_eq, Complex.ext_iff] at hl₂_ne
      simp only [sub_eq_zero] at h h₁
      simp_all only [ne_eq, and_self, not_true_eq_false]}
    simp_all only [ne_eq, false_or, mul_zero, zero_eq_mul]
    simp only [Complex.ext_iff, Complex.sub_re, h, Complex.mul_re, Complex.ofReal_re, h₁, mul_zero,
      Complex.ofReal_im, Complex.sub_im, zero_mul, sub_self, Complex.mul_im, add_zero, true_and]
    refine ⟨(l₁.z₁.im - l₁.z₂.im) / (l₂.z₁.im - l₂.z₂.im), (div_mul_cancel₀ (l₁.z₁.im - l₁.z₂.im) this).symm⟩
  by_cases h₂: l₂.z₁.im - l₂.z₂.im = 0
  . simp only [h₂, zero_mul, zero_eq_mul] at h
    have: l₂.z₁.re - l₂.z₂.re ≠  0 := by{
      by_contra h
      simp only [ne_eq, Complex.ext_iff] at hl₂_ne
      simp only [sub_eq_zero] at h h₂
      simp_all only [ne_eq, and_self, not_true_eq_false]}
    simp_all only [ne_eq, not_false_eq_true, or_false, zero_mul, mul_eq_zero]
    simp only [Complex.ext_iff, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, h₂, mul_zero, sub_zero, h, Complex.mul_im, zero_mul,
      add_zero, and_true]
    refine ⟨(l₁.z₁.re - l₁.z₂.re) / (l₂.z₁.re - l₂.z₂.re), (div_mul_cancel₀ (l₁.z₁.re - l₁.z₂.re) this).symm⟩
  refine ⟨(l₁.z₁.re - l₁.z₂.re) / (l₂.z₁.re - l₂.z₂.re), Complex.ext_iff.mpr ⟨?_, ?_⟩⟩ <;> simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, zero_mul, sub_zero, Complex.mul_im, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, Complex.sub_re, zero_mul, add_zero]
  . rw [div_mul_cancel₀ (l₁.z₁.re - l₁.z₂.re) h₁]
  . have h: (↑l₁.z₁.re - ↑l₁.z₂.re)/ (↑l₂.z₁.re - ↑l₂.z₂.re) = (↑l₁.z₁.im - ↑l₁.z₂.im)/ (↑l₂.z₁.im - ↑l₂.z₂.im) := by
      rw [propext (div_eq_div_iff h₁ h₂), mul_comm]
      exact h
    rw [h, div_mul_cancel₀ (l₁.z₁.im - l₁.z₂.im) h₂]


lemma eq_of_parallel {hl₁_ne : l₁.z₁ ≠ l₁.z₂} (h : parallel' l₁ l₂) (hx : ∃z, z ∈ l₁.points ∩ l₂.points ): l₁.points = l₂.points := by
  --rw [@Mathlib.Tactic.PushNeg.ne_empty_eq_nonempty, Set.nonempty_def,] at hx --! for (h: l₁.points ∩ l₂.points ≠ ∅)
  obtain ⟨x, hx₁, hx₂⟩ := hx
  ext z
  simp only [line_pionts_iff l₁ x hx₁, line_pionts_iff l₂ x hx₂, Set.mem_setOf_eq]
  unfold parallel' direction_vector at h
  obtain ⟨k, hk⟩ := h
  refine ⟨?_,?_⟩ <;> intro h <;> obtain ⟨t, ht⟩ := h
  . use t * k
    push_cast
    rw [mul_assoc, ←hk]
    exact ht
  . use t / k
    have : k ≠ 0 := by
      by_contra h'
      simp only [h', Complex.ofReal_zero, zero_mul, sub_eq_zero] at hk
      contradiction
    have: Invertible (k:ℂ) := by exact invertibleOfNonzero (Complex.ofReal_ne_zero.mpr this)
    rw[←@invOf_mul_eq_iff_eq_mul_left _  _ (l₁.z₁ - l₁.z₂) (l₂.z₁ - l₂.z₂) k this, invOf_eq_inv (k:ℂ)] at hk
    push_cast
    ring_nf at hk ⊢
    rw[←sub_mul, hk, add_comm, mul_comm]
    exact ht

end DirectionVectorsOfLines_parallel

-- section safekeeping
-- variable (l₁ l₂ : line) (hl₁_ne : l₁.z₁ ≠ l₁.z₂) (hl₂_ne : l₂.z₁ ≠ l₂.z₂)

-- noncomputable def line_arg (l : line) : ℝ := Complex.arg (l.z₁ - l.z₂)

-- lemma line_parallel (h : line_arg l₁ = line_arg l₂ ) : parallel l₁ l₂ := by
--   unfold parallel
--   use (l₁.z₂ - l₂.z₂)
--   ext x
--   simp [line.points]
--   refine ⟨?_,?_⟩
--   . intro hl₁
--     have  div: (Complex.abs (l₂.z₁ - l₂.z₂)) ≠  0 := by
--       by_contra h
--       rw [AbsoluteValue.map_sub_eq_zero_iff] at h
--       exact hl₂_ne h
--     simp [line_arg] at h
--     obtain ⟨t, ht⟩ := hl₁
--     use (t * Complex.abs (l₁.z₁ - l₁.z₂) / Complex.abs (l₂.z₁ - l₂.z₂))
--     rw[←ht]
--     ring_nf
--     suffices (t * Complex.abs (l₁.z₁ - l₁.z₂) * (Complex.abs (l₂.z₁ - l₂.z₂))⁻¹) * (l₂.z₁ - l₂.z₂) + l₁.z₂ = t * (l₁.z₁ - l₁.z₂) + l₁.z₂ by {
--       calc _ = (t * Complex.abs (l₁.z₁ - l₁.z₂) * (Complex.abs (l₂.z₁ - l₂.z₂))⁻¹) * (l₂.z₁ - l₂.z₂) + l₁.z₂ := by push_cast; ring_nf
--         _ = t * (l₁.z₁ - l₁.z₂) + l₁.z₂ := by rw[this]
--         _ = l₁.z₁ * ↑t + (l₁.z₂ - l₁.z₂ * ↑t):= by push_cast; ring_nf
--     }
--     rw [add_right_cancel_iff, Complex.ext_abs_arg_iff]
--     refine ⟨?_,?_⟩
--     . simp only [Complex.ofReal_inv, map_mul, Complex.abs_ofReal, Complex.abs_abs, map_inv₀]
--       exact inv_mul_cancel_right₀ div (|t| * Complex.abs (l₁.z₁ - l₁.z₂))
--     . by_cases ht: t = 0
--       . rw[ht]
--         simp
--       by_cases ht_pos: 0 < t
--       . have : 0 < (t * (Complex.abs (l₁.z₁ - l₁.z₂)) * (Complex.abs (l₂.z₁ - l₂.z₂))⁻¹) :=  by
--           rw [mul_pos_iff]
--           left
--           refine ⟨ ?_, ?_⟩
--           . rw [mul_pos_iff]
--             left
--             refine ⟨ ht_pos, ?_⟩
--             rw [AbsoluteValue.pos_iff, sub_ne_zero]
--             exact hl₁_ne
--           . rw [inv_pos, AbsoluteValue.pos_iff, sub_ne_zero]
--             exact hl₂_ne
--         norm_cast
--         rw[Complex.arg_real_mul _ ht_pos,  Complex.arg_real_mul _ this]
--         symm
--         exact h
--       -- . have Ne_zero: (↑t * ↑(Complex.abs (l₁.z₁ - l₁.z₂)) * ↑(Complex.abs (l₂.z₁ - l₂.z₂))⁻¹ * (l₂.z₁ - l₂.z₂)) ≠ 0 := by
--       --     simp only [Complex.ofReal_inv, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, ht,
--       --       AbsoluteValue.map_sub_eq_zero_iff, hl₁_ne, or_self, inv_eq_zero, hl₂_ne, sub_eq_zero,
--       --       not_false_eq_true]
--       --   have Ne_zero': (↑t * (l₁.z₁ - l₁.z₂)) ≠ 0 := by
--       --     simp only [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, ht, sub_eq_zero, hl₁_ne, or_self,
--       --       not_false_eq_true]
--       . have ht_pos: 0 < -t := by
--           rw [neg_pos]
--           rw [Mathlib.Tactic.PushNeg.not_gt_eq] at ht_pos
--           exact lt_of_le_of_ne ht_pos ht
--         suffices (- (↑t * ↑(Complex.abs (l₁.z₁ - l₁.z₂)) * ↑(Complex.abs (l₂.z₁ - l₂.z₂))⁻¹ * (l₂.z₁ - l₂.z₂))).arg = (- (↑t * (l₁.z₁ - l₁.z₂))).arg by {
--           by_cases h_im: 0 < (l₁.z₁ - l₁.z₂).im
--           . have im_neg :  (↑t * (l₁.z₁ - l₁.z₂)).im < 0 := by
--               rw [Complex.im_ofReal_mul, mul_neg_iff]
--               right
--               refine ⟨Left.neg_pos_iff.mp ht_pos, h_im⟩
--             have im_neg' : (↑t * ↑(Complex.abs (l₁.z₁ - l₁.z₂)) * ↑(Complex.abs (l₂.z₁ - l₂.z₂))⁻¹ * (l₂.z₁ - l₂.z₂)).im < 0:= by
--               norm_cast
--               rw [Complex.im_ofReal_mul, mul_neg_iff]
--               right
--               refine ⟨?_,?_⟩
--               . rw [mul_neg_iff]
--                 right
--                 refine ⟨?_, ?_⟩
--                 . rw [mul_neg_iff]
--                   right
--                   refine ⟨?_, ?_⟩
--                   . exact Left.neg_pos_iff.mp ht_pos
--                   . rw [AbsoluteValue.pos_iff, sub_ne_zero]
--                     exact hl₁_ne
--                 . rw [inv_pos, AbsoluteValue.pos_iff , sub_ne_zero]
--                   exact hl₂_ne
--               . rw [Complex.arg_eq_arg_iff] at h
--                 rw[← h]
--                 . norm_cast
--                   rw [Complex.im_ofReal_mul, mul_pos_iff]
--                   left
--                   refine ⟨?_, h_im⟩
--                   rw [div_pos_iff]
--                   left
--                   refine ⟨?_, ?_⟩
--                   . rw [AbsoluteValue.pos_iff , sub_ne_zero]
--                     exact hl₂_ne
--                   . rw [ AbsoluteValue.pos_iff , sub_ne_zero]
--                     exact hl₁_ne
--                 . rw [sub_ne_zero]
--                   exact hl₁_ne
--                 . rw [sub_ne_zero]
--                   exact hl₂_ne
--             rw[←@add_right_cancel_iff _ _ _ (Real.pi), ←Complex.arg_neg_eq_arg_add_pi_of_im_neg im_neg', ←Complex.arg_neg_eq_arg_add_pi_of_im_neg im_neg]
--             exact this
--           . rw[not_lt] at h_im
--             by_cases h_im': (l₁.z₁ - l₁.z₂).im = 0
--             . norm_cast
--               rw[←Complex.arg_coe_angle_eq_iff, Complex.arg_mul_coe_angle, Complex.arg_mul_coe_angle, h, add_right_cancel_iff]
--               . rw[Complex.arg_ofReal_of_neg, Complex.arg_ofReal_of_neg]
--                 . exact Left.neg_pos_iff.mp ht_pos
--                 . rw [mul_neg_iff]
--                   right
--                   refine ⟨?_, ?_⟩
--                   . rw[mul_neg_iff]
--                     right
--                     refine ⟨?_, ?_⟩
--                     . exact Left.neg_pos_iff.mp ht_pos
--                     . rw [AbsoluteValue.pos_iff, sub_ne_zero]
--                       exact hl₁_ne
--                   . rw [inv_pos, AbsoluteValue.pos_iff, sub_ne_zero]
--                     exact hl₂_ne
--               . norm_cast
--               . exact sub_ne_zero_of_ne hl₁_ne
--               . simp only [Complex.ofReal_mul, Complex.ofReal_inv, ne_eq, mul_eq_zero,
--                 Complex.ofReal_eq_zero, AbsoluteValue.map_sub_eq_zero_iff, inv_eq_zero, not_or]
--                 refine ⟨⟨ ht, hl₁_ne⟩, hl₂_ne⟩
--               . exact sub_ne_zero_of_ne hl₂_ne
--             have im_pos : 0 < (↑t * (l₁.z₁ - l₁.z₂)).im := by
--               rw [Complex.im_ofReal_mul, mul_pos_iff]
--               right
--               refine ⟨?_, ?_⟩
--               . exact Left.neg_pos_iff.mp ht_pos
--               . exact lt_of_le_of_ne h_im h_im'
--             have im_pos' : 0 < (↑t * ↑(Complex.abs (l₁.z₁ - l₁.z₂)) * ↑(Complex.abs (l₂.z₁ - l₂.z₂))⁻¹ * (l₂.z₁ - l₂.z₂)).im := by
--               norm_cast
--               rw [Complex.im_ofReal_mul, mul_pos_iff]
--               right
--               refine ⟨?_, ?_⟩
--               . rw [mul_neg_iff]
--                 right
--                 refine ⟨?_, ?_⟩
--                 . rw [mul_neg_iff]
--                   right
--                   refine ⟨?_, ?_⟩
--                   . exact Left.neg_pos_iff.mp ht_pos
--                   . rw [AbsoluteValue.pos_iff, sub_ne_zero]
--                     exact hl₁_ne
--                 . rw [inv_pos, AbsoluteValue.pos_iff , sub_ne_zero]
--                   exact hl₂_ne
--               . rw [Complex.arg_eq_arg_iff] at h
--                 rw[← h]
--                 . norm_cast
--                   rw [Complex.im_ofReal_mul, mul_neg_iff]
--                   left
--                   refine ⟨?_, lt_of_le_of_ne h_im h_im'⟩
--                   rw [div_pos_iff]
--                   left
--                   refine ⟨?_, ?_⟩
--                   . rw [AbsoluteValue.pos_iff , sub_ne_zero]
--                     exact hl₂_ne
--                   . rw [ AbsoluteValue.pos_iff , sub_ne_zero]
--                     exact hl₁_ne
--                 . rw [sub_ne_zero]
--                   exact hl₁_ne
--                 . rw [sub_ne_zero]
--                   exact hl₂_ne
--             rw[←@add_right_cancel_iff _ _ _ (-Real.pi),Mathlib.Tactic.RingNF.add_neg, Mathlib.Tactic.RingNF.add_neg , ←Complex.arg_neg_eq_arg_sub_pi_of_im_pos im_pos', ←Complex.arg_neg_eq_arg_sub_pi_of_im_pos im_pos]
--             exact this
--           -- push_cast
--           -- rw[←Complex.arg_neg_coe_angle Ne_zero, ←Complex.arg_neg_coe_angle Ne_zero']
--           -- exact this
--         }
--         have : 0 < (-t * (Complex.abs (l₁.z₁ - l₁.z₂)) * (Complex.abs (l₂.z₁ - l₂.z₂))⁻¹) := by
--           rw [mul_pos_iff]
--           left
--           refine ⟨ ?_, ?_⟩
--           . rw [mul_pos_iff]
--             left
--             refine ⟨ ht_pos, ?_⟩
--             rw [AbsoluteValue.pos_iff, sub_ne_zero]
--             exact hl₁_ne
--           . rw [inv_pos, AbsoluteValue.pos_iff, sub_ne_zero]
--             exact hl₂_ne
--         simp_rw[neg_mul_eq_neg_mul]
--         norm_cast
--         rw[Complex.arg_real_mul _ ht_pos,  Complex.arg_real_mul _ this]
--         symm
--         exact h
--   . intro hl₂
--     obtain ⟨t, ht⟩ := hl₂
--     by_cases ht_zero: t = 0
--     . use t
--       simp only [ht_zero, Complex.ofReal_zero, zero_mul, sub_zero, one_mul, zero_add, ← ht,
--         add_sub_cancel]
--     have div: Complex.abs (l₁.z₁ - l₁.z₂) ≠ 0 := by
--       by_contra h
--       rw [AbsoluteValue.map_sub_eq_zero_iff] at h
--       exact hl₁_ne h
--     by_cases ht_pos: 0 < t
--     . ring_nf
--       ring_nf at ht
--       use (t * Complex.abs (l₂.z₁ - l₂.z₂) / Complex.abs (l₁.z₁ - l₁.z₂))
--       rw[←ht, add_right_cancel_iff, ←mul_sub, ←mul_sub, div_eq_mul_inv,  Complex.ext_abs_arg_iff]
--       refine ⟨?_, ?_ ⟩
--       . simp  only [Complex.ofReal_mul, Complex.ofReal_inv, map_mul, Complex.abs_ofReal,
--         Complex.abs_abs, map_inv₀]
--         rw [inv_mul_cancel_right₀ div (|t| * Complex.abs (l₂.z₁ - l₂.z₂))]
--       . have: 0 < t * Complex.abs (l₂.z₁ - l₂.z₂) * (Complex.abs (l₁.z₁ - l₁.z₂))⁻¹ := by
--           rw [mul_pos_iff]
--           left
--           refine ⟨ ?_, ?_⟩
--           . rw [mul_pos_iff]
--             left
--             refine ⟨ ht_pos, ?_⟩
--             rw [AbsoluteValue.pos_iff, sub_ne_zero]
--             exact hl₂_ne
--           . rw [inv_pos, AbsoluteValue.pos_iff, sub_ne_zero]
--             exact hl₁_ne
--         rw[Complex.arg_real_mul _ ht_pos,  Complex.arg_real_mul _ this]
--         exact h
--     . have ht_pos: 0 < -t := by
--           rw [neg_pos]
--           rw [Mathlib.Tactic.PushNeg.not_gt_eq] at ht_pos
--           exact lt_of_le_of_ne ht_pos ht_zero
--       ring_nf
--       ring_nf at ht
--       use ((t) * Complex.abs (l₂.z₁ - l₂.z₂) / Complex.abs (l₁.z₁ - l₁.z₂))
--       rw[←ht, add_right_cancel_iff, ←mul_sub, ←mul_sub, div_eq_mul_inv,  Complex.ext_abs_arg_iff]
--       refine ⟨?_, ?_ ⟩
--       . simp only [neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_inv,
--         map_neg_eq_map, map_mul, Complex.abs_ofReal, Complex.abs_abs, map_inv₀]
--         rw [inv_mul_cancel_right₀ div (|t| * Complex.abs (l₂.z₁ - l₂.z₂))]
--       . have: 0 < -t * Complex.abs (l₂.z₁ - l₂.z₂) * (Complex.abs (l₁.z₁ - l₁.z₂))⁻¹ := by
--           rw [mul_pos_iff]
--           left
--           refine ⟨ ?_, ?_⟩
--           . rw [mul_pos_iff]
--             left
--             refine ⟨ ht_pos, ?_⟩
--             rw [AbsoluteValue.pos_iff, sub_ne_zero]
--             exact hl₂_ne
--           . rw [inv_pos, AbsoluteValue.pos_iff, sub_ne_zero]
--             exact hl₁_ne

--         sorry

-- lemma line_parallel' (h : line_arg l₁ = - line_arg l₂) : parallel l₁ l₂ := by
--   sorry


-- lemma line_parallel_iff (l₁ l₂ : line): parallel l₁ l₂ ↔ ∃ k, l₁.z₁ - l₁.z₂ = k * (l₂.z₁ - l₂.z₂) := by
--   constructor
--   . intro h
--     obtain ⟨z, hz⟩ := h
--     sorry
--   . rintro ⟨z, hz⟩
--     use z
--     sorry

-- lemma line_parallel_imp (par: parallel l₁ l₂) (z x y :ℂ) (hx: x ∈ l₁.points) (hy: y ∈ l₂.points ) (hz: z = x - y): l₁.points = {x + z | x ∈ l₂.points} := by
--   unfold parallel at par
--   obtain ⟨zp, hzp⟩ := par


--   sorry




-- lemma line_piont_imp_eq (l₁ l₂ : line) (par: parallel l₁ l₂) (h : ∃ x, x ∈ l₁.points ∩ l₂.points) : l₁.points = l₂.points := by
--   unfold parallel at par
--   obtain ⟨z, hz⟩ := par
--   obtain ⟨x, hx₁, hx₂⟩ := h
--   -- unfold line.points at hx₁ hx₂
--   -- simp only [Set.mem_setOf_eq] at hx₁ hx₂
--   -- obtain ⟨t, ht⟩ := hx₁
--   -- obtain ⟨s, hs⟩ := hx₂
--   have hzero: z = 0 := by
--     have : ↑x + z ∈ l₁.points := by
--       simp only [Set.mem_setOf_eq, add_left_inj, exists_eq_right, hx₂, hz]
--     obtain ⟨t, ht⟩ := this
--     obtain ⟨s, hs⟩ := hx₁
--     rw [←hs, add_comm _ z] at ht

--     have : z = (t-s) * l₁.z₁ - (t-s) * l₁.z₂ := by
--       symm
--       calc _ = ↑t * l₁.z₁ + (1 - ↑t) * l₁.z₂ - (↑s * l₁.z₁ + (1 - ↑s) * l₁.z₂) := by ring_nf
--         _ = z := by exact sub_eq_of_eq_add ht
--     sorry
--   simp only [hzero, add_zero, exists_eq_right, Set.setOf_mem_eq] at hz
--   exact hz

-- end safekeeping
