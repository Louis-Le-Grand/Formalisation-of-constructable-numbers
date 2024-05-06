import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

def circle_with_radius_metric (c r₁ r₂: ℂ) := Metric.sphere c (dist r₁ r₂)
noncomputable def circle_with_radius_euklid (c: ℂ)(r: ℝ)(h: 0 < r) :
  EuclideanGeometry.Sphere ℂ := { center := c, radius := r }

def line_through_two_points (z₁ z₂: ℂ) : Set ℂ:= {(t : ℂ) * z₁ + (1-t) * z₂ | (t : ℝ)}

#check NormedAddTorsor

def intersection_line_line (z₁ z₂ z₃ z₄ :ℂ) :=
  line_through_two_points z₁ z₂ ∩ line_through_two_points z₃ z₄

def intersection_line_circle (c r₁ r₂ z₁ z₂ :ℂ) :=
  line_through_two_points z₁ z₂ ∩ circle_with_radius_metric c r₁ r₂

def intersection_circle_circle (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) :=
  circle_with_radius_metric c₁ r₁ r₂ ∩ circle_with_radius_metric c₂ r₃ r₄

--TODO: Do I need to repeat the proofs
-- dist c1 c2 > r1 + r2 --> no intersection
-- dist c1 c2 + r1 < r2 --> no intersection
-- dist c1 c2 + r2 < r1 --> no intersection
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

-- dist c1 c2 + r1 = r2 --> one intersection
-- dist c1 c2 + r2 = r1 --> one intersection
-- dist c1 c2 = r1 + r2 --> one intersection
lemma int_cir_cir_4 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₁ r₂)=(dist r₃ r₄)):
  .card (intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄) = 1 := by
    rw [@Nat.le_antisymm_iff]; constructor; sorry; sorry

lemma int_cir_cir_5 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₃ r₄)=(dist r₁ r₂)):
  .card (intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄) = 1 := by sorry

lemma int_cir_cir_6 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist r₁ r₂)+(dist r₃ r₄)=(dist c₁ c₂)):
  .card (intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄) = 1 := by sorry

lemma int_cir_cir_4' (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₁ r₂)=(dist r₃ r₄)):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ = {c₁ + (c₁-c₂)/(dist c₁ c₂)*(dist r₁ r₂)} := by sorry
lemma int_cir_cir_5' (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₃ r₄)=(dist r₁ r₂)):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ = {c₂ + (r₃/(r₃+r₄))*(c₁-c₂)} := by sorry
lemma int_cir_cir_6' (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist r₁ r₂)+(dist r₃ r₄)=(dist c₁ c₂)):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ = {c₁ + (r₁/(r₁+r₂))*(c₂-c₁)} := by sorry


-- dist c1 c2 + r1 < r2  --> two intersections given one ther is a nother on
-- dist c1 c2 + r2 < r1  --> two intersections
-- r1 + r2 < dist c1 c2  --> two intersections
lemma int_cir_cir_7 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₁ r₂)<(dist r₃ r₄)):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ =
  {c₁ + (r₁/(r₁+r₂))*(c₂-c₁), c₂ + (r₃/(r₃+r₄))*(c₁-c₂)} := by sorry
lemma int_cir_cir_8 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist c₁ c₂)+(dist r₃ r₄)<(dist r₁ r₂)):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ =
  {c₁ + (r₁/(r₁+r₂))*(c₂-c₁), c₂ + (r₃/(r₃+r₄))*(c₁-c₂)} := by sorry
lemma int_cir_cir_9 (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) (h: (dist r₁ r₂)+(dist r₃ r₄)<(dist c₁ c₂)):
  intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ =
  {c₁ + (r₁/(r₁+r₂))*(c₂-c₁), c₂ + (r₃/(r₃+r₄))*(c₁-c₂)} := by sorry

-- Definition of construction of M_inf
def Z_M (M : Set ℂ) : Set ℂ :=
  M ∪ {z : ℂ | ∃ c₁ r₁ r₂ c₂ r₃ r₄ : ℂ, z ∈ intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄} ∪
  {z : ℂ | ∃ c r₁ r₂ z₁ z₂ : ℂ, z ∈ intersection_line_circle c r₁ r₂ z₁ z₂} ∪
  {z : ℂ | ∃ z₁ z₂ z₃ z₄ : ℂ, z ∈ intersection_line_line z₁ z₂ z₃ z₄}

def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => Z_M (M_I M n)

def M_inf (M : Set ℂ) : Set ℂ :=  ⋃ (n : ℕ), M_I M n


@[simp] lemma M_0 (M : Set ℂ) : M_I M 0 = M := rfl

lemma M_in_Z_M (M : Set ℂ) : M ⊆ Z_M M := by
  unfold Z_M; intro x; intro hx; left; left; left; exact hx

lemma M_I_Monotone (M : Set ℂ) : ∀n, M_I M n ⊆ M_I M (n+1) := by
  intro n; apply M_in_Z_M

lemma M_I_Monotone_elm (M : Set ℂ)(n : ℕ) : ∀ x, x ∈ M_I M n → x ∈ M_I M (Nat.succ n) := by
  intro n; apply M_in_Z_M

lemma M_in_M_I (M : Set ℂ) : ∀n, M ⊆ M_I M n := by
  intro n; induction n; simp [M_I]; exact fun ⦃a⦄ a => a;
  case succ n hn => apply le_trans hn; apply M_I_Monotone

lemma M_I_Monotone' (M : Set ℂ)(n m : ℕ)(h: n ≤ m) :  M_I M n ⊆ M_I M m := by
  apply monotone_nat_of_le_succ; apply M_I_Monotone; exact h

lemma M_I_Monotone_elm' (M : Set ℂ)(n m : ℕ)(h: n ≤ m) : ∀ x, x ∈ M_I M n → x ∈ M_I M m := by
  intro x; apply M_I_Monotone' M n m h

lemma M_I_in_M_inf (M : Set ℂ) :∀m, M_I M m ⊆ M_inf M := by
  unfold M_inf; intro m; exact Set.subset_iUnion_of_subset m fun ⦃a⦄ a => a
