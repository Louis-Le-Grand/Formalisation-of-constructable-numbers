import Mathlib.Geometry.Euclidean.Sphere.Basic

def circle_with_radius_metric (c r₁ r₂: ℂ) := Metric.sphere c (dist r₁ r₂)

def line_through_two_points (z₁ z₂: ℂ) : Set ℂ:= {(t : ℂ) * z₁ + (1-t) * z₂ | (t : ℝ)}

def intersection_line_line (z₁ z₂ z₃ z₄ :ℂ) :=
  line_through_two_points z₁ z₂ ∩ line_through_two_points z₃ z₄

def intersection_line_circle (c r₁ r₂ z₁ z₂ :ℂ) :=
  line_through_two_points z₁ z₂ ∩ circle_with_radius_metric c r₁ r₂

def intersection_circle_circle (c₁ r₁ r₂ c₂ r₃ r₄ : ℂ) :=
  circle_with_radius_metric c₁ r₁ r₂ ∩ circle_with_radius_metric c₂ r₃ r₄

def ICL_M (M : Set ℂ) : Set ℂ :=
  M ∪ {z : ℂ | ∃ c₁ r₁ r₂ c₂ r₃ r₄ : M, z ∈ intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄} ∪
  {z : ℂ | ∃ c r₁ r₂ z₁ z₂ : M, z ∈ intersection_line_circle c r₁ r₂ z₁ z₂} ∪
  {z : ℂ | ∃ z₁ z₂ z₃ z₄ : M, z ∈ intersection_line_line z₁ z₂ z₃ z₄}

def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => ICL_M (M_I M n)

def M_inf (M : Set ℂ) : Set ℂ :=  ⋃ (n : ℕ), M_I M n

lemma M_in_ICL_M (M : Set ℂ) : M ⊆ ICL_M M := by
  unfold ICL_M; intro x; intro hx; left; left; left; exact hx

lemma M_inf_in_M_I (M : Set ℂ) : ∀ x : M_inf M, ∃ n, ↑x ∈ (M_I M n):= by
  intro x; apply Set.mem_iUnion.mp; exact Subtype.coe_prop x


lemma int_ll_in_M_inf (M : Set ℂ): ∀ z₁ z₂ z₃ z₄: M_inf M, intersection_line_line z₁ z₂ z₃ z₄ ⊆ M_inf M := by
  intro z₁ z₂ z₃ z₄; have h: ∃ n: ℕ, ↑z₁ ∈ M_I M n ∧ ↑z₂ ∈ M_I M n ∧ ↑z₃ ∈ M_I M n ∧ ↑z₄ ∈ M_I M n := by sorry
  sorry

lemma int_lc_in_M_inf (M : Set ℂ): ∀ c r₁ r₂ z₁ z₂:M_inf M, intersection_line_circle c r₁ r₂ z₁ z₂ ⊆ M_inf M := by sorry

lemma int_cc_in_M_inf (M : Set ℂ): ∀ c₁ r₁ r₂ c₂ r₃ r₄:M_inf M, intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ ⊆ M_inf M := by sorry


lemma M_in_M_inf (M : Set ℂ) : ICL_M (M_inf M) = M_inf M := by sorry
/-   rw [@Set.Subset.antisymm_iff]; constructor; case right => exact M_in_ICL_M (M_inf M)
  rw [ICL_M]; apply Set.union_subset; apply Set.union_subset; apply Set.union_subset; exact
  fun ⦃a⦄ a ↦ a; refine Set.setOf_subset.mpr ?left.sr.sr.tr.a; intro x hx; apply int_cc_in_M_inf;
  obtain ⟨c₁, r₁, r₂, c₂, r₃, r₄, hx⟩ := hx; sorry
  refine Set.setOf_subset.mpr ?left.sr.tr.a; intro x hx; apply int_cc_in_M_inf;
  obtain ⟨c₁, r₁, r₂, z₁, z₂, hx⟩ := hx; sorry
  refine Set.setOf_subset.mpr ?left.tr.a; intro x hx; apply int_lc_in_M_inf;
  obtain ⟨c, r₁, r₂, z₁, z₂, hx⟩ := hx; sorry -/
