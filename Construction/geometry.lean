import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

def circle_with_radius_metric (c r₁ r₂: ℂ) := Metric.sphere c (dist r₁ r₂)
noncomputable def circle_with_radius_euklid (c: ℂ)(r: ℝ)(h: 0 < r) :
  EuclideanGeometry.Sphere ℂ := { center := c, radius := r }

def line_through_two_points (z₁ z₂: ℂ) : Set ℂ:= {(t : ℂ) * z₁ + (1-t) * z₂ | (t : ℝ)}

def intersection_line_line (z₁ z₂ z₃ z₄ :ℂ) :=
  line_through_two_points z₁ z₂ ∩ line_through_two_points z₃ z₄

/-def intersection_lined (l₁ :line_through_two_points z₁ z₂)
(l₂: line_through_two_points z₃ z₄): Set ℂ := l₁ ∩ l₂-/

def intersection_line_circle (c r₁ r₂ z₁ z₂ :ℂ) :=
  line_through_two_points z₁ z₂ ∩ circle_with_radius_metric c r₁ r₂

def intersection_circle_circle (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) :=
  circle_with_radius_metric c₁ r₁ r₂ ∩ circle_with_radius_metric c₂ r₃ r₄

def Z_M (M : Set ℂ) : Set ℂ :=
  M ∪ {z : ℂ | ∃ c₁ r₁ r₂ c₂ r₃ r₄ : ℂ, z ∈ intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄} ∪
  {z : ℂ | ∃ c r₁ r₂ z₁ z₂ : ℂ, z ∈ intersection_line_circle c r₁ r₂ z₁ z₂} ∪
  {z : ℂ | ∃ z₁ z₂ z₃ z₄ : ℂ, z ∈ intersection_line_line z₁ z₂ z₃ z₄}

def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => Z_M (M_I M n)

def M_inf (M : Set ℂ) : Set ℂ :=  ⋃ (n : ℕ), M_I M n


@[simp] lemma M_0 (M : Set ℂ) : M_I M 0 = M := rfl

@[simp] lemma M_in_Z_M (M : Set ℂ) : M ⊆ Z_M M := by
  unfold Z_M; intro x; intro hx; left; left; left; exact hx

@[simp] lemma M_I_Monotone (M : Set ℂ) : ∀n, M_I M n ⊆ M_I M (n+1) := by
  intro n; induction n; simp [M_I]; unfold M_I; apply M_in_Z_M

@[simp] lemma M_I_Monotone_elm (M : Set ℂ)(n : ℕ) : ∀ x, x ∈ M_I M n → x ∈ M_I M (Nat.succ n) := by
  intro n; induction n; simp [M_I]; unfold M_I; apply M_in_Z_M

@[simp] lemma M_in_M_I (M : Set ℂ) : ∀n, M ⊆ M_I M n := by
  intro n; induction n; simp [M_I]; exact fun ⦃a⦄ a => a;
  case succ n hn => apply le_trans hn; simp

@[simp] lemma M_I_Monotone' (M : Set ℂ)(n m : ℕ)(h: n ≤ m) :  M_I M n ⊆ M_I M m := by
  sorry --monotomnie veralgmeiner
/-  induction n; simp
  case succ n hn => sorry
    by_cases hc: Nat.succ n = m
    · simp [hc]; exact fun ⦃a⦄ a => a
    · simp[Nat.le_iff_lt_or_eq, hc] at h
      apply le_trans (b:=M_I M (Nat.pred m))
      . sorry
      . convert M_I_Monotone; constructor; intro hn' M' n'; use M_I M (Nat.pred n) -/

@[simp] lemma M_I_Monotone_elm' (M : Set ℂ)(n m : ℕ)(h: n ≤ m) : ∀ x, x ∈ M_I M n → x ∈ M_I M m := by
  intro x; apply M_I_Monotone' M n m h

@[simp] lemma M_I_in_M_inf (M : Set ℂ) :∀m, M_I M m ⊆ M_inf M := by
  unfold M_inf; intro m; exact Set.subset_iUnion_of_subset m fun ⦃a⦄ a => a
