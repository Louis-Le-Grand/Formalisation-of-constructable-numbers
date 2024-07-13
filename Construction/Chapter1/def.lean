import Mathlib.Data.Complex.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic


namespace Construction
structure line where
  (z₁ z₂ : ℂ)

def line.points (l: line) : Set ℂ:= {(t : ℂ) * l.z₁ + (1-t) * l.z₂ | (t : ℝ)}

lemma line_not_eq_if (l₁ l₂: line) (h: ∃ x, x ∈ l₁.points ∧ x ∉ l₂.points) :  l₁.points ≠ l₂.points := by
  obtain ⟨x, hx₁, hx₂⟩ := h
  rw [Ne.eq_def, Set.ext_iff, Mathlib.Tactic.PushNeg.not_forall_eq]
  use x
  simp only [hx₁, hx₂, iff_false, not_true_eq_false, not_false_eq_true]

lemma line_not_eq_if' (l₁ l₂: line) (h: ∃ x, x ∈ l₂.points ∧ x ∉ l₁.points) :  l₁.points ≠ l₂.points := by
  symm
  exact line_not_eq_if l₂ l₁ h

def parallel (l₁ l₂ : line) := ∃ z, l₁.points = {x + z | x ∈ l₂.points}

--TODO: not in Blueprint
lemma parallel_self (l : line) : parallel l l := by
  use 0
  simp
--TODO: not in Blueprint
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


def L (M:Set ℂ): Set line := {l |∃ z₁ z₂, l = {z₁ := z₁, z₂ := z₂} ∧ z₁ ∈  M ∧ z₂ ∈ M ∧ z₁ ≠ z₂}
def C (M:Set ℂ): Set circle := {c |∃ z r₁ r₂, c = {c:=z, r:=(dist r₁ r₂)} ∧ z ∈ M ∧ r₁ ∈ M ∧ r₂ ∈ M}

--TODO: not in Blueprint
lemma c_in_C_M (M:Set ℂ): c ∈ C M ↔  ∃ z r₁ r₂, c = {c:=z, r:=(dist r₁ r₂)} ∧ z ∈ M ∧ r₁ ∈ M ∧ r₂ ∈ M := by
  unfold C
  simp

--TODO: not in Blueprint
lemma l_in_L_M (M:Set ℂ): l ∈ L M ↔ ∃ z₁ z₂, l = {z₁ := z₁, z₂ := z₂} ∧ z₁ ∈ M ∧ z₂ ∈ M ∧ z₁ ≠ z₂ := by
  unfold L
  simp

lemma l_in_L_M_imp (M:Set ℂ)(l: line) (hl: l ∈ L M ): l.z₁ ∈ M ∧ l.z₂ ∈ M := by
  obtain ⟨z₁, z₂, hl, hz₁, hz₂, _⟩ := hl
  constructor
  rw [hl]
  exact hz₁
  rw [hl]
  exact hz₂

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
