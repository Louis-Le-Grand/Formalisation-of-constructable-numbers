import Mathlib.Data.Complex.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Complex

example  (a : ℝ)(h: ¬(-↑a * I).exp = -1): im ((exp (a * I / 2)) / (exp (a * I) + 1)) = 0 := by

  have g: (((a).cos + (a).sin * I + 1) * ((a).cos - (a).sin * I + 1)) = 2*(1+ (a).cos) := by
    ring_nf
    simp only [ofReal_cos, ofReal_sin, I_sq, mul_neg, mul_one, sub_neg_eq_add, cos_sq_add_sin_sq]
    ring_nf

  have : (↑(a / 2).sin * (↑a.cos + 1) - ↑(a / 2).cos * ↑a.sin) * I = 0 := by
    have hcos :  (a).cos = (a/2).cos ^ 2 - (a/2).sin ^ 2 := by rw [← Real.cos_two_mul', mul_div_left_comm, div_self (by norm_num), mul_one]
    have hsin :  (a).sin = 2 * (a/2).sin * (a/2).cos := by rw [← Real.sin_two_mul, mul_div_left_comm, div_self (by norm_num), mul_one]
    rw [hsin, hcos, mul_add]
    norm_cast
    rw[mul_sub]
    calc _ = ((a/2).sin * (a/2).cos^2 - 2 * (a/2).cos^2 * (a/2).sin - (a/2).sin * (a/2).sin^2 + (a/2).sin) * I := by push_cast; ring_nf
      _ = ((a/2).sin * ((a/2).cos^2 - 2 * (a/2).cos^2  - (a/2).sin^2 + 1)) * I := by ring_nf
      _ = ((a/2).sin * (- ((a/2).cos^2 + (a/2).sin^2) + 1)) * I := by ring_nf
      _ = ((a/2).sin * (- 1 + 1)) * I := by norm_cast; simp only [Real.cos_sq_add_sin_sq, add_left_neg,
        mul_zero, ofReal_zero, zero_mul, Int.reduceNegSucc, Int.cast_zero]
      _ = 0 := by ring_nf

  calc _ = ((↑a / 2*I).exp / ((↑a * I).exp + 1)).im := by ring_nf
  _ = (((a / 2).cos + (a / 2).sin * I) / ((a).cos + (a).sin * I + 1)).im := by
    rw [exp_mul_I, exp_mul_I]; norm_cast
  _ = ((((a / 2).cos + (a / 2).sin * I)  / ((a).cos + (a).sin * I + 1)) * (((a).cos - (a).sin * I + 1)/((a).cos - (a).sin * I + 1))).im := by rw [div_self (by push_cast; rw [cos_sub_sin_I a]; rw [@Ne.eq_def]; rw [@add_eq_zero_iff_eq_neg]; exact h), mul_one]
  _ = ((((a / 2).cos + (a / 2).sin * I) * ((a).cos - (a).sin * I + 1)) / (((a).cos + (a).sin * I + 1) * ((a).cos - (a).sin * I + 1))).im := by rw[mul_div_mul_comm]
  _ = ((((a / 2).cos + (a / 2).sin * I) * ((a).cos - (a).sin * I + 1)) / (2*(1+ (a).cos))).im := by rw[g]
  _ = (((a / 2).cos * ((a).cos + 1) - (a / 2).sin  * (a).sin * I^2 - (a / 2).cos * (a).sin * I  + (a / 2).sin * ((a).cos+1) * I) / (2*(1+ (a).cos))).im := by ring_nf
  _ = (((a / 2).cos * ((a).cos + 1) + (a / 2).sin  * (a).sin  - (a / 2).cos * (a).sin * I  + (a / 2).sin * ((a).cos+1) * I) / (2*(1+ (a).cos))).im := by simp only [I_sq, mul_neg, mul_one, sub_neg_eq_add]
  _ = (((a / 2).cos * ((a).cos + 1) + (a / 2).sin  * (a).sin  + ((a / 2).sin * ((a).cos+1) - (a / 2).cos * (a).sin) * I) / (2*(1+ (a).cos))).im := by ring_nf
  _ = (((a / 2).cos * ((a).cos + 1) + (a / 2).sin  * (a).sin  + (0:ℂ) ) / (2*(1+ (a).cos))).im := by rw [this]
  _ = (((a / 2).cos * ((a).cos + 1) + (a / 2).sin  * (a).sin) / (2*(1+ (a).cos)):ℂ).im := by simp only [ofReal_cos,
    ofReal_div, ofReal_ofNat, ofReal_sin, add_zero]
  _ = 0 := by norm_cast
