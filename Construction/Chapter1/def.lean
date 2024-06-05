import Mathlib.Data.Complex.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic


structure line where
  (z₁ z₂ : ℂ)

def line.points (l: line) : Set ℂ:= {(t : ℂ) * l.z₁ + (1-t) * l.z₂ | (t : ℝ)}


structure circle where
  (c : ℂ)
  (r : ℝ)

def circle.points (c: circle) := Metric.sphere c.c c.r


def L (M:Set ℂ): Set line := {l |∃ z₁ z₂, l = {z₁ := z₁, z₂ := z₂} ∧ z₁ ∈  M ∧ z₂ ∈ M}
def C (M:Set ℂ): Set circle := {c |∃ z r₁ r₂, c = {c:=z, r:=(dist r₁ r₂)} ∧ z ∈ M ∧ r₁ ∈ M ∧ r₂ ∈ M}


lemma c_in_C_M (M:Set ℂ): c ∈ C M ↔  ∃ z r₁ r₂, c = {c:=z, r:=(dist r₁ r₂)} ∧ z ∈ M ∧ r₁ ∈ M ∧ r₂ ∈ M := by
  unfold C; simp


def ill (M:Set ℂ): Set ℂ := { z  |∃l₁ ∈ L M, ∃ l₂ ∈ L M,  z ∈ l₁.points ∩ l₂.points}
def ilc (M:Set ℂ): Set ℂ := { z  |∃c ∈ C M, ∃ l ∈ L M,  z ∈ c.points ∩ l.points}
def icc (M:Set ℂ): Set ℂ := { z  |∃c₁ ∈ C M, ∃ c₂ ∈ C M,  z ∈ c₁.points ∩ c₂.points}


def Z_M (M : Set ℂ) : Set ℂ := M ∪ ill M ∪ ilc M ∪ icc M

def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => Z_M (M_I M n)

def M_inf (M : Set ℂ) : Set ℂ :=  ⋃ (n : ℕ), M_I M n
