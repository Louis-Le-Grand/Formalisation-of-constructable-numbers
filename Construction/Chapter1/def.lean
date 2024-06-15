import Mathlib.Data.Complex.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic


structure line where
  (z₁ z₂ : ℂ)

def line.points (l: line) : Set ℂ:= {(t : ℂ) * l.z₁ + (1-t) * l.z₂ | (t : ℝ)}

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

lemma parallel_basis(l₁ l₂ : line) : l₁.z₁ - l₂.z₁ = l₁.z₂ - l₂.z₂ → parallel l₁ l₂  := by
  intro h
  unfold parallel
  use l₁.z₁ - l₂.z₁
  unfold line.points
  ext x
  simp
  constructor
  . intro hx
    obtain ⟨t, ht⟩ := hx
    have hr: ∃ r:ℝ,r = t*(l₁.z₁ - l₁.z₂) / (l₂.z₁ - l₂.z₂):= by
      have h: (t*(l₁.z₁ - l₁.z₂) / (l₂.z₁ - l₂.z₂)).im = 0 := by
        sorry
      sorry
    obtain ⟨r, hr⟩ := hr
    use r
    rw [←ht, sub_mul, ←@add_sub_assoc, ←@add_sub_assoc]
    sorry --TODO: Umformung
  sorry

structure circle where
  (c : ℂ)
  (r : ℝ)

def circle.points (c: circle) := Metric.sphere c.c c.r


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

def ill (M:Set ℂ): Set ℂ := { z  |∃l₁ ∈ L M, ∃ l₂ ∈ L M,  z ∈ l₁.points ∩ l₂.points}
def ilc (M:Set ℂ): Set ℂ := { z  |∃c ∈ C M, ∃ l ∈ L M,  z ∈ c.points ∩ l.points}
def icc (M:Set ℂ): Set ℂ := { z  |∃c₁ ∈ C M, ∃ c₂ ∈ C M,  z ∈ c₁.points ∩ c₂.points}


def ICL_M (M : Set ℂ) : Set ℂ := M ∪ ill M ∪ ilc M ∪ icc M

def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => ICL_M (M_I M n)

def M_inf (M : Set ℂ) : Set ℂ :=  ⋃ (n : ℕ), M_I M n
