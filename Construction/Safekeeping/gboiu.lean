import Construction.Chapter1.basic_construction
import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.Normal
import Construction.Chapter2.PR14987



def conj_set (M : Set ℂ) : Set ℂ := {starRingEnd ℂ z | z ∈ M}

class ConjClosed (M : Set ℂ) : Prop where
  equal: M = conj_set M

open Complex IntermediateField ComplexConjugate Construction Polynomial

variable (L : Subfield ℂ) [ConjClosed L]

lemma ir_L (z : ℂ) (h : z ∈ L): ↑z.re ∈ L := by sorry


lemma im_L (z : ℂ) (h : z ∈ L): z.im * Complex.I ∈ L := by sorry


lemma distSq_L (z₁ z₂ : ℂ) (h₁ : z₁ ∈ L) (h₂ : z₂ ∈ L): ↑(Complex.normSq (z₁ - z₂)) ∈ L := by sorry

lemma ilc_L  (c: Construction.circle) (l: line) (hc: 0 ≤ c.r): z ∈ c.points ∩ l.points ↔
    let a := (l.z₁.re - l.z₂.re)^2 - (I*l.z₁.im - I*l.z₂.im)^2
    let b := 2*((l.z₁.re - l.z₂.re) * (l.z₂.re - c.c.re) - (I*l.z₁.im - I*l.z₂.im) * (I*l.z₂.im-I*c.c.im))
    let c := (l.z₂.re - c.c.re)^2 - (I*l.z₂.im - I*c.c.im)^2 - c.r^2
    ∃ ι:ℝ, ι^2 * a + ι * b + c = 0  ∧ ι * l.z₁ + (1- ι) * l.z₂ = z := by
    sorry

variable {F: Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

-- lemma K_le_K_adjion' {x : E} (h: x ∈ ↑F) (α : E): ↑x ∈ F⟮α⟯:= by
--     unfold IntermediateField.adjoin
--     apply Subfield.subset_closure
--     apply Or.inl
--     simp

lemma sq_add_sq_eq_zero (a b :ℝ) : a^2 + b^2 = 0 ↔ a = 0 ∧ b = 0 := by
  refine ⟨?_, ?_⟩ <;> intro h
  . rw [add_eq_zero_iff_eq_neg] at h
    have _ : 0 ≤ a^2 ∧  0 ≤ b^2:= by
      refine ⟨pow_two_nonneg a, pow_two_nonneg b⟩
    have h : a^2 = 0 ∧ b^2 = 0:= by
      refine ⟨(by linarith) , (by linarith)⟩
    simp_rw [pow_eq_zero_iff (by exact Ne.symm (Nat.zero_ne_add_one 1))] at h
    exact h
  . simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]

lemma ilc_L' (z : ℂ) (h : z ∈ ilc L): ∃ ω ∈ L, ∃ x : ℂ, x * x = ω ∧ z ∈ L⟮x⟯ := by
  obtain ⟨c, hc, l, hl, hz⟩ := h
  have: 0 ≤ c.r := by sorry
  rw[ilc_L _ _ this] at hz
  obtain ⟨ι, ⟨hι, hz⟩⟩ := hz
  have hlz₁: l.z₁ ∈ L := by sorry
  have hlz₂: l.z₂ ∈ L := by sorry
  have hcc: c.c ∈ L := by sorry
  have hcr: (c.r:ℂ)^2 ∈ L := by sorry
  let u := (l.z₁.re - l.z₂.re)^2 - (l.z₁.im*I - l.z₂.im*I)^2
  let v := 2*((l.z₁.re - l.z₂.re) * (l.z₂.re - c.c.re) - (l.z₁.im*I - l.z₂.im*I) * (l.z₂.im*I-c.c.im*I))
  let w := (l.z₂.re - c.c.re)^2 - (l.z₂.im*I - c.c.im*I)^2 - c.r^2
  have hu: u ∈ L := by sorry
  have hv: v ∈ L := by sorry
  have hw: w ∈ L := by sorry
  use (v^2 / (4 * u^2) - w / u)
  refine ⟨sorry, ⟨(v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ), sorry, ?_⟩⟩
  have cast_L {x : ℂ}(h: x ∈ L): x ∈ (↥L)⟮(v ^ 2 / (4 * u ^ 2) - w / u) ^ (1 / 2:ℂ)⟯ := by sorry
  . rw [←hz]
    suffices (ι:ℂ) ∈ (↑L )⟮(v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ)⟯ by sorry
    let f : (Polynomial ℂ) :=  C u * X ^ 2 + C v * X + C w
    have: u ≠ 0 := by sorry
    have f_degree: degree f = 2 := by sorry
    have f_ne_zero: f ≠ 0 := by sorry
    have : ↑ι ∈ f.roots := by sorry
    have : ↑(Multiset.card (f.roots)) ≤ 2 := by sorry
    have : f.roots = { - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ),  - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ) } := by
      unfold roots
      simp only [f_ne_zero, ↓reduceDIte, f_degree, Nat.cast_le_ofNat, one_div,
        Multiset.insert_eq_cons]

      --! Need to prove that the roots of f are the roots of f


      sorry
    sorry
