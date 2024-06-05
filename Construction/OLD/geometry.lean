import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import Mathlib.Analysis.Complex.Arg

def circle_with_radius_metric (c r₁ r₂: ℂ) := Metric.sphere c (dist r₁ r₂)

def line_through_two_points (z₁ z₂: ℂ) : Set ℂ:= {(t : ℂ) * z₁ + (1-t) * z₂ | (t : ℝ)}

#check NormedAddTorsor

--Todo try modify cir to two points

def intersection_line_line (z₁ z₂ z₃ z₄ :ℂ) :=
  line_through_two_points z₁ z₂ ∩ line_through_two_points z₃ z₄

def intersection_line_circle (c r₁ r₂ z₁ z₂ :ℂ) :=
  line_through_two_points z₁ z₂ ∩ circle_with_radius_metric c r₁ r₂

def intersection_circle_circle (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) :=
  circle_with_radius_metric c₁ r₁ r₂ ∩ circle_with_radius_metric c₂ r₃ r₄

-- r₁ + r₂ < dist c₁ c₂ --> no intersection
lemma int_cir_cir_1' (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist r₁ r₂)+(dist r₃ r₄)<(dist c₁ c₂)):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ = ∅ := by
    by_contra h'; rw [@Set.eq_empty_iff_forall_not_mem] at h'; simp at h'; obtain ⟨x, hx⟩ := h'
    simp [intersection_circle_circle, circle_with_radius_metric] at hx; obtain ⟨hx1, hx2⟩ := hx
    have h1: dist r₁ r₂ + dist r₃ r₄ ≥ dist c₁ c₂ := by
      rw[←hx1, ← hx2, ←Complex.dist_eq, ←Complex.dist_eq, dist_comm]; apply dist_triangle
    rw[lt_iff_not_ge] at h; exact h h1

lemma int_cir_cir_1 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ)(h: (dist r₁ r₂)+(dist r₃ r₄)<(dist c₁ c₂)):
  .card (intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄) = 0 := by
    rw [int_cir_cir_1' (h:=h)]; simp

-- dist c₁ c₂ + r₁ < r₂ --> no intersection
lemma int_cir_cir_2' (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₁ r₂)<(dist r₃ r₄)):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ = ∅ := by
    by_contra h'; rw [@Set.eq_empty_iff_forall_not_mem] at h'; simp at h'; obtain ⟨x, hx⟩ := h'
    simp [intersection_circle_circle, circle_with_radius_metric] at hx; obtain ⟨hx1, hx2⟩ := hx
    have h1: dist c₁ c₂ + dist r₁ r₂ ≥ dist r₃ r₄ := by
      rw[←hx1, ← hx2, ←Complex.dist_eq, ←Complex.dist_eq, add_comm]; apply dist_triangle
    rw[lt_iff_not_ge] at h; exact h h1

lemma int_cir_cir_2 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₁ r₂)<(dist r₃ r₄)):
  .card (intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄) = 0 := by
    rw [int_cir_cir_2' (h:=h)]; simp

-- dist c₁ c₂ + r₁ < r₂ --> no intersection
lemma int_cir_cir_3' (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₃ r₄)<(dist r₁ r₂)):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ = ∅ := by
    by_contra h'; rw [@Set.eq_empty_iff_forall_not_mem] at h'; simp at h'; obtain ⟨x, hx⟩ := h'
    simp [intersection_circle_circle, circle_with_radius_metric] at hx; obtain ⟨hx1, hx2⟩ := hx
    have h1: dist c₁ c₂ + dist r₃ r₄ ≥ dist r₁ r₂ := by
      rw[←hx1, ← hx2, ←Complex.dist_eq, ←Complex.dist_eq, add_comm]; nth_rewrite 2 [dist_comm];
      apply dist_triangle
    rw[lt_iff_not_ge] at h; exact h h1

lemma int_cir_cir_3 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₃ r₄)<(dist r₁ r₂)):
  .card (intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄) = 0 := by
    rw [int_cir_cir_3' (h:=h)]; simp

-- dist c₁ c₂ + r₁ = r₂ and circel not equal --> one intersection
lemma int_cir_cir_4' (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ)(h:(dist c₁ c₂)+(dist r₁ r₂)=(dist r₃ r₄)) (neq:c₁≠c₂):
intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ = {c₁ + (c₁-c₂)/(dist c₁ c₂)*(dist r₁ r₂)} := by
  rw[subset_antisymm_iff]; constructor; case right =>
    unfold intersection_circle_circle; simp; by_cases distr: dist r₁ r₂ = 0;
    constructor; unfold circle_with_radius_metric; simp
    rw[←Complex.dist_eq, div_self, one_mul]; rw[dist_ne_zero]; exact neq
    unfold circle_with_radius_metric; simp; rw[←h, distr]; simp; rw[Complex.dist_eq]
    constructor; unfold circle_with_radius_metric; simp
    rw[←Complex.dist_eq, div_self, one_mul]; rw[dist_ne_zero]; exact neq
    unfold circle_with_radius_metric; simp; rw[Complex.dist_eq, Complex.dist_eq, ←h]
    rw[add_comm, add_sub_assoc]
    rw[Complex.abs_add_eq (x:=((c₁ - c₂) / ↑(Complex.abs (c₁ - c₂)) * ↑(Complex.abs (r₁ - r₂))))
    (y:=(c₁-c₂)), @AbsoluteValue.map_mul, map_div₀ Complex.abs (c₁-c₂) (↑(Complex.abs (c₁-c₂))),
    Complex.abs_of_nonneg, div_self, one_mul, Complex.abs_of_nonneg, Complex.dist_eq,
    Complex.dist_eq, add_comm]; simp; rw[←Complex.dist_eq, dist_ne_zero]; exact neq; simp;
    rw[mul_comm, Complex.arg_real_mul (r:=(Complex.abs (r₁ - r₂)))
    ((c₁ - c₂) / ↑(Complex.abs (c₁ - c₂))), div_eq_mul_inv, mul_comm]
    norm_cast; rw[Complex.arg_real_mul (r:=(Complex.abs (c₁ - c₂))⁻¹) (c₁ - c₂)];
    rw[←Complex.dist_eq, inv_pos, dist_pos]; exact neq; simp at *;
    rw[@sub_eq_iff_eq_add, zero_add]; exact distr
  case left =>
    by_contra hn; simp at *; obtain ⟨x, hx, hn⟩ := hn
    have hn': x = c₁ + (c₁ - c₂) / ↑(Complex.abs (c₁ - c₂)) * ↑(Complex.abs (r₁ - r₂)) := by
      unfold intersection_circle_circle circle_with_radius_metric at hx; simp at hx;
      obtain ⟨hx1, hx2⟩ := hx; rw[←h, ←Complex.dist_eq] at hx2; symm at hx2;
      rw[← @eq_sub_iff_add_eq' (c:=dist c₁ c₂)] at hx2; rw[hx2, @eq_sub_iff_add_eq'] at hx1;
      sorry --TODO: finish
    contradiction

lemma int_cir_cir_4 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₁ r₂)=(dist r₃ r₄))(neq: c₁ ≠ c₂):
  .card (intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄) = 1 := by
  rw[int_cir_cir_4' (h:=h) (neq:=neq)]; simp

--TODO show comm int

-- dist c₁ c₂ + r₂ = r₁ and circel not equal --> one intersection
lemma int_cir_cir_5' (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₃ r₄)=(dist r₁ r₂)) (neq: c₁ ≠ c₂):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ = {c₂ + (c₁-c₂)/(dist c₁ c₂)*(dist r₃ r₄)} := by sorry
/-   rw[subset_antisymm_iff]; constructor; case right =>
    unfold intersection_circle_circle; simp; by_cases distr: dist r₃ r₄ = 0;
    constructor; unfold circle_with_radius_metric; simp; rw[←h, distr,←Complex.dist_eq]; simp; rw[dist_comm]
    unfold circle_with_radius_metric; simp; rw[←Complex.dist_eq, div_self, one_mul]; rw[dist_ne_zero]; exact neq
    constructor;case neg.right =>
      unfold circle_with_radius_metric; simp
      rw[←Complex.dist_eq, div_self, one_mul]; rw[dist_ne_zero]; exact neq
    unfold circle_with_radius_metric; simp; rw[Complex.dist_eq, Complex.dist_eq, ←h]
    rw[add_comm, add_sub_assoc]
    rw[Complex.abs_add_eq (x:=((c₁ - c₂) / ↑(Complex.abs (c₁ - c₂)) * ↑(Complex.abs (r₃ - r₄))))
    (y:=(c₂-c₁)), @AbsoluteValue.map_mul, map_div₀ Complex.abs (c₁-c₂) (↑(Complex.abs (c₁-c₂))),
    Complex.abs_of_nonneg, div_self, one_mul, Complex.abs_of_nonneg, Complex.dist_eq,
    Complex.dist_eq, add_comm]; simp; rw[←Complex.dist_eq,←Complex.dist_eq, dist_comm];simp;
    rw[←Complex.dist_eq, dist_ne_zero]; exact neq; simp;
    rw[mul_comm, Complex.arg_real_mul (r:=(Complex.abs (r₃ - r₄)))
    ((c₁ - c₂) / ↑(Complex.abs (c₁ - c₂))), div_eq_mul_inv, mul_comm]
    norm_cast; rw[Complex.arg_real_mul (r:=(Complex.abs (c₁ - c₂))⁻¹) (c₁ - c₂)];sorry --TODO: flip c₁ c₂ somewhere, this is not correct
    rw[←Complex.dist_eq, inv_pos, dist_pos]; exact neq; simp at *;
    rw[@sub_eq_iff_eq_add, zero_add]; exact distr
  case left => sorry -/

lemma int_cir_cir_5 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₃ r₄)=(dist r₁ r₂))(neq: c₁ ≠ c₂):
  .card (intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄) = 1 := by
  rw[int_cir_cir_5' (h:=h) (neq:=neq)]; simp

-- dist r₁ r₂ + dist r₃ r₄ = dist c₁ c₂ --> one intersection
lemma int_cir_cir_6 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist r₁ r₂)+(dist r₃ r₄)=(dist c₁ c₂)):
  .card (intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄) = 1 := by sorry

lemma int_cir_cir_6' (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist r₁ r₂)+(dist r₃ r₄)=(dist c₁ c₂)):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ = {c₁ + (r₁/(r₁+r₂))*(c₂-c₁)} := by sorry

--Todo formoulate as: given one ther is a nother on
--TODO: check lemma 7 and 8
-- dist c₁ c₂ + r₁ < r₂ --> two intersection
lemma int_cir_cir_7 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₁ r₂)<(dist r₃ r₄)):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ =
  {c₁ + (r₁/(r₁+r₂))*(c₂-c₁), c₂ + (r₃/(r₃+r₄))*(c₁-c₂)} := by sorry

-- dist c₁ c₂ + r₂ < r₁ --> two intersection
lemma int_cir_cir_8 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₃ r₄)<(dist r₁ r₂)):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ =
  {c₁ + (r₁/(r₁+r₂))*(c₂-c₁), c₂ + (r₃/(r₃+r₄))*(c₁-c₂)} := by sorry

--TODO Fix naming
--TODO; add lemma, which states that that you are always in case 1 - 10
-- circle are equal
lemma int_cir_cir_10 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: c₁ = c₂ ∧ dist r₁ r₂ = dist r₃ r₄):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ = circle_with_radius_metric c₁ r₁ r₂:= by sorry

lemma int_cir_cir_10_symm (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: c₁ = c₂ ∧ dist r₁ r₂ = dist r₃ r₄):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ = circle_with_radius_metric c₂ r₃ r₄:= by sorry

-- Intersection of circle is finite if the circles are not equal
lemma int_cir_cir_finite (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: c₁ ≠ c₂ ∨ dist r₁ r₂ ≠ dist r₃ r₄):
  .card (intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄) ≤ 2 := by sorry

-- Intersection of circle isn't empty if the not case 1,2,3
lemma int_cir_cir_not_empty (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: ¬((dist r₁ r₂)+(dist r₃ r₄)<(dist c₁ c₂) ∨
  (dist c₁ c₂)+(dist r₁ r₂)<(dist r₃ r₄) ∨ (dist c₁ c₂)+(dist r₃ r₄)<(dist r₁ r₂))):
  ∃ x, x ∈ (intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄)  := by sorry
