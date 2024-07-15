import Mathlib.Data.Complex.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic


/-
# First we define a line trough two points
  - `x`,`y` are two points in `ℂ`
  - `{λx+ (1-λ)y | λ ∈ ℝ}` is the set of points on the line trough x and y
-/
structure line where
  (z₁ z₂ : ℂ)

def line.points (l: line) : Set ℂ:= {(t : ℂ) * l.z₁ + (1-t) * l.z₂ | (t : ℝ)}

/-
# Next we define a circle with center `c` and radius `r`
  - `c` is a point in `ℂ`
  - `r` is a real number
  - `Metric.sphere c r` is the set of points on the circle with center `c` and radius `r`
-/
structure circle where
  (c : ℂ)
  (r : ℝ)

def circle.points (c: circle) : Set ℂ := Metric.sphere c.c c.r
noncomputable def circle.points' (c: circle) := (⟨c.c, c.r⟩ : EuclideanGeometry.Sphere ℂ)

/-
# Set of lienes and circles in `M`
  - `L M` is the set of lines trough two points in `M`
  - `C M` is the set of circles with center in `M`
-/
def L (M:Set ℂ): Set line := {l |∃ z₁ z₂, l = {z₁ := z₁, z₂ := z₂} ∧ z₁ ∈  M ∧ z₂ ∈ M ∧ z₁ ≠ z₂}
def C (M:Set ℂ): Set circle := {c |∃ z r₁ r₂, c = {c:=z, r:=(dist r₁ r₂)} ∧ z ∈ M ∧ r₁ ∈ M ∧ r₂ ∈ M}

/-
# Intersection of lines and circles
  - `ill M` is the set of points that are on two lines in `M`
  - `ilc M` is the set of points that are on a line and a circle in `M`
  - `icc M` is the set of points that are on two circles in `M`
  - `ICL_M M` is the set of points that are in `M` or in `ill M` or in `ilc M` or in `icc M`
-/
def ill (M:Set ℂ): Set ℂ := { z  |∃l₁ ∈ L M, ∃ l₂ ∈ L M,  z ∈ l₁.points ∩ l₂.points ∧ l₁.points ≠ l₂.points}
def ilc (M:Set ℂ): Set ℂ := { z  |∃c ∈ C M, ∃ l ∈ L M,  z ∈ c.points ∩ l.points}
def icc (M:Set ℂ): Set ℂ := { z  |∃c₁ ∈ C M, ∃ c₂ ∈ C M,  z ∈ c₁.points ∩ c₂.points ∧ c₁.points' ≠ c₂.points'}

def ICL_M (M : Set ℂ) : Set ℂ := M ∪ ill M ∪ ilc M ∪ icc M

/-
# i-th iteration of the construction
  - `M_I M n` is the set of points that are in `M` or in `ill M` or in `ilc M` or in `icc M` for `n` iterations
-/
def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => ICL_M (M_I M n)

/-
# The set of constructable points
  Is the limes of `M_I M n` as `n` goes to infinity wich can also be written as union.
-/
def M_inf (M : Set ℂ) : Set ℂ :=  ⋃ (n : ℕ), M_I M n
