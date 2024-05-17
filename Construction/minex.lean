import Mathlib.Geometry.Euclidean.Sphere.Basic

def circle_with_radius_metric (c r₁ r₂: ℂ) := Metric.sphere c (dist r₁ r₂)

def intersection_circle_circle (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) :=
  circle_with_radius_metric c₁ r₁ r₂ ∩ circle_with_radius_metric c₂ r₃ r₄

def Z_M (M : Set ℂ) : Set ℂ :=
  M ∪ {z : ℂ | ∃ c₁ r₁ r₂ c₂ r₃ r₄ : M, z ∈ intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄}

def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => Z_M (M_I M n)

def M_inf (M : Set ℂ) : Set ℂ :=  ⋃ (n : ℕ), M_I M n

lemma M_I_in_M_inf (M : Set ℂ)(m: ℕ): M_I M m ⊆ M_inf M := by
  unfold M_inf; exact Set.subset_iUnion_of_subset m fun ⦃a⦄ a => a

lemma Int_cc_in_M_inf'' (M : Set ℂ)(c₁ r₁ r₂ c₂ r₃ r₄ : M_inf M): intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ ⊆ M_inf M := by
  have h₁: ∃ n, ↑c₁ ∈ M_I M n:= by sorry
  have h₂: ∃ n, ↑r₁ ∈ M_I M n:= by sorry
  have h₃: ∃ n, ↑r₂ ∈ M_I M n:= by sorry
  have h₄: ∃ n, ↑c₂ ∈ M_I M n:= by sorry
  have h₅: ∃ n, ↑r₃ ∈ M_I M n:= by sorry
  have h₆: ∃ n, ↑r₄ ∈ M_I M n:= by sorry
  rw [@Set.subset_def]; intro x hx; apply M_I_in_M_inf;
  sorry; sorry --! her I want to use the biggiest n := max {nᵢ such that hᵢ holds}
