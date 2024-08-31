import Mathlib.Data.Complex.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic


namespace Construction
structure line where
  (z₁ z₂ : ℂ)

def line.points (l: line) : Set ℂ:= {(t : ℂ) * l.z₁ + (1-t) * l.z₂ | (t : ℝ)}

--not bp
lemma line_not_eq_if (l₁ l₂: line) (h: ∃ x, x ∈ l₁.points ∧ x ∉ l₂.points) :  l₁.points ≠ l₂.points := by
  obtain ⟨x, hx₁, hx₂⟩ := h
  rw [Ne.eq_def, Set.ext_iff, Mathlib.Tactic.PushNeg.not_forall_eq]
  use x
  simp only [hx₁, hx₂, iff_false, not_true_eq_false, not_false_eq_true]

--not bp
lemma line_not_eq_if' (l₁ l₂: line) (h: ∃ x, x ∈ l₂.points ∧ x ∉ l₁.points) :  l₁.points ≠ l₂.points := by
  symm
  exact line_not_eq_if l₂ l₁ h

structure circle where
  (c : ℂ)
  (r : ℝ)

def circle.points (c: circle) := Metric.sphere c.c c.r
noncomputable def circle.points' (c: circle) := (⟨c.c, c.r⟩ : EuclideanGeometry.Sphere ℂ)

lemma circle_points_eq (c: circle) : c.points = c.points' := by
  simp only [circle.points, circle.points']

lemma circle_not_eq_iff {c₁ c₂ : Construction.circle} (h: c₁.c ≠ c₂.c): c₁.points' ≠ c₂.points' := by
  rw[@EuclideanGeometry.Sphere.ne_iff ℂ _ c₁.points' c₂.points']
  left
  exact h

lemma circle_not_eq_iff_radius {c₁ c₂ : Construction.circle} (h: c₁.r ≠ c₂.r): c₁.points' ≠ c₂.points' := by
  rw[@EuclideanGeometry.Sphere.ne_iff ℂ _ c₁.points' c₂.points']
  right
  exact h

def L (M:Set ℂ): Set line := {l |∃ z₁ z₂, l = {z₁ := z₁, z₂ := z₂} ∧ z₁ ∈  M ∧ z₂ ∈ M ∧ z₁ ≠ z₂}
def C (M:Set ℂ): Set circle := {c |∃ z r₁ r₂, c = {c:=z, r:=(dist r₁ r₂)} ∧ z ∈ M ∧ r₁ ∈ M ∧ r₂ ∈ M}

lemma c_in_C_M (M:Set ℂ): c ∈ C M ↔  ∃ z r₁ r₂, c = {c:=z, r:=(dist r₁ r₂)} ∧ z ∈ M ∧ r₁ ∈ M ∧ r₂ ∈ M := by
  unfold C
  simp

lemma l_in_L_M (M:Set ℂ): l ∈ L M ↔ ∃ z₁ z₂, l = {z₁ := z₁, z₂ := z₂} ∧ z₁ ∈ M ∧ z₂ ∈ M ∧ z₁ ≠ z₂ := by
  unfold L
  simp

--not bp
lemma l_in_L_M_imp (M:Set ℂ)(l: line) (hl: l ∈ L M ): l.z₁ ∈ M ∧ l.z₂ ∈ M := by
  obtain ⟨z₁, z₂, hl, hz₁, hz₂, _⟩ := hl
  constructor
  rw [hl]
  exact hz₁
  rw [hl]
  exact hz₂

--not bp
lemma l_in_L_M_imp' (M:Set ℂ)(l: line) (hl: l ∈ L M ): l.z₁ ≠ l.z₂ := by
  obtain ⟨z₁, z₂, hl, _, _, Noteq⟩ := hl
  rw[hl]
  exact Noteq

def ill (M:Set ℂ): Set ℂ := { z  |∃l₁ ∈ L M, ∃ l₂ ∈ L M,  z ∈ l₁.points ∩ l₂.points ∧ l₁.points ≠ l₂.points}
def ilc (M:Set ℂ): Set ℂ := { z  |∃c ∈ C M, ∃ l ∈ L M,  z ∈ c.points ∩ l.points}
def icc (M:Set ℂ): Set ℂ := { z  |∃c₁ ∈ C M, ∃ c₂ ∈ C M,  z ∈ c₁.points ∩ c₂.points ∧ c₁.points' ≠ c₂.points'}


def ICL_M (M : Set ℂ) : Set ℂ := M ∪ ill M ∪ ilc M ∪ icc M

def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => ICL_M (M_I M n)

def M_inf (M : Set ℂ) : Set ℂ :=  ⋃ (n : ℕ), M_I M n

lemma L_mono (M N : Set ℂ) (h: M ⊆ N) : Construction.L M ⊆ Construction.L N := by
  unfold Construction.L
  simp only [Set.iUnion_subset_iff, Set.subset_def]
  intro l hl
  obtain ⟨z₁, z₂, hl, hz₁, hz₂, hne⟩ := hl
  refine ⟨z₁, z₂, hl,  h hz₁, h hz₂, hne⟩

lemma C_mono (M N : Set ℂ) (h: M ⊆ N) : Construction.C M ⊆ Construction.C N := by
  unfold Construction.C
  simp only [Set.iUnion_subset_iff, Set.subset_def]
  intro c hc
  obtain ⟨z, r₁, r₂, hl, hz, hr₁, hr₂⟩ := hc
  refine ⟨z, r₁, r₂, hl,  h hz, h hr₁, h hr₂⟩

lemma ill_mono (M N : Set ℂ) (h: M ⊆ N) : ill M ⊆ ill N := by
  unfold ill
  simp only [Set.iUnion_subset_iff, Set.subset_def]
  intro x hx
  obtain ⟨l₁, hl₁, l₂, hl₂, hx, hlne⟩ := hx
  refine ⟨l₁, ?_, l₂, ?_, hx, hlne⟩
  apply L_mono M N h hl₁
  apply L_mono M N h hl₂

lemma ilc_mono (M N : Set ℂ) (h: M ⊆ N) : ilc M ⊆ ilc N := by
  unfold ilc
  simp only [Set.iUnion_subset_iff, Set.subset_def]
  intro x hx
  obtain ⟨c, hc, l, hl, hx, hlne⟩ := hx
  refine ⟨c, ?_, l, ?_, hx, hlne⟩
  apply C_mono M N h hc
  apply L_mono M N h hl

lemma icc_mono (M N : Set ℂ) (h: M ⊆ N) : icc M ⊆ icc N := by
  unfold icc
  simp only [Set.iUnion_subset_iff, Set.subset_def]
  intro x hx
  obtain ⟨c₁, hc₁, c₂, hc₂, hx, hlne⟩ := hx
  refine ⟨c₁, ?_, c₂, ?_, hx, hlne⟩
  apply C_mono M N h hc₁
  apply C_mono M N h hc₂
