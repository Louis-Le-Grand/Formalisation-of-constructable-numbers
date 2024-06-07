import Construction.Chapter1.set_MInf

--(h₁: 1 ∈ M)
-- Konstruction Schröer
lemma z_neg_M_inf (M: Set ℂ)(h₀: (0:ℂ)∈ M)(z : ℂ)(hz : z ∈ (M_inf M)) : -z ∈ (M_inf M) := by
  by_cases z0:(z=0)
  simp[z0]; apply M_M_inf; exact h₀
  let l : line := {z₁ := 0, z₂ := z}
  let c : circle := {c := 0, r := (dist 0 z)}
  have hl : l ∈ L (M_inf M) := by unfold L; use 0; use z; constructor; simp; constructor; apply M_M_inf M h₀; constructor; exact hz; symm; simp[z0]
  have hc : c ∈ C (M_inf M) := by rw[c_in_C_M]; use 0; use 0; use z; constructor; simp_all only [dist_zero_left, Complex.norm_eq_abs, l, c]; constructor; apply M_M_inf M h₀; constructor; apply M_M_inf M h₀; exact hz
  have hlc : -z ∈ c.points ∩ l.points := by {rw [@Set.mem_inter_iff]; constructor; simp[circle.points]; simp[line.points]; use 2; ring_nf; calc  -(2 * z) + z = -z := by ring}
  apply ilc_M_inf M; unfold ilc; rw [@Set.mem_setOf]; use c; constructor; exact hc ; use l

-- Konstruction Schröer
lemma add_M_Inf (M: Set ℂ)(h₀: (0:ℂ)∈ M)(z₁ z₂ : ℂ)(hz₁ : z₁ ∈ (M_inf M))(hz₂ : z₂ ∈ (M_inf M)): z₁ + z₂ ∈ (M_inf M) := by
  let c₁ : circle := {c := z₁, r := (dist 0 z₂)}
  let c₂ : circle := {c := z₂, r := (dist 0 z₁)}
  have hc₁ : c₁ ∈ C (M_inf M) := by rw[c_in_C_M]; use z₁; use 0; use z₂; constructor; simp_all only [dist_zero_left, Complex.norm_eq_abs, c₁]; constructor; exact hz₁; constructor; apply M_M_inf M h₀; exact hz₂
  have hc₂ : c₂ ∈ C (M_inf M) := by rw[c_in_C_M]; use z₂; use 0; use z₁; constructor; simp_all only [dist_zero_left, Complex.norm_eq_abs, c₂]; constructor; exact hz₂; constructor; apply M_M_inf M h₀; exact hz₁
  have hcc : z₁ + z₂ ∈ c₁.points ∩ c₂.points := by rw [@Set.mem_inter_iff];  simp[circle.points]
  apply icc_M_inf M; unfold icc; rw [@Set.mem_setOf]; use c₁; constructor; exact hc₁; use c₂

lemma sub_M_Inf (M: Set ℂ)(h₀: (0:ℂ)∈ M)(z₁ z₂ : ℂ)(hz₁ : z₁ ∈ (M_inf M))(hz₂ : z₂ ∈ (M_inf M)): z₁ - z₂ ∈ (M_inf M) := by
  have hz : z₁ - z₂ = z₁ + (-z₂) := by ring
  rw [hz]; apply add_M_Inf M h₀ z₁ (-z₂) hz₁; apply z_neg_M_inf M h₀ z₂ hz₂

-- Konstruction Schröer
lemma conj_M_Inf (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1 ∈ M)(z : ℂ)(hz : z ∈ (M_inf M)): (starRingEnd ℂ) z ∈ (M_inf M) := by
  let c₀ : circle := {c := 0, r := (dist 0 z)}
  let c₁ : circle := {c := 1, r := (dist 1 z)}
  have hc₀ : c₀ ∈ C (M_inf M) := by rw[c_in_C_M]; use 0; use 0; use z; constructor; simp_all only [dist_zero_left, Complex.norm_eq_abs, c₀]; constructor; apply M_M_inf M h₀; constructor; apply M_M_inf M h₀; exact hz
  have hc₁ : c₁ ∈ C (M_inf M) := by rw[c_in_C_M]; use 1; use 1; use z; constructor; simp_all only [dist_zero_left, Complex.norm_eq_abs, c₁]; constructor; apply M_M_inf M h₁; constructor; apply M_M_inf M h₁; exact hz
  have hcc : (starRingEnd ℂ) z ∈ c₀.points ∩ c₁.points := by rw [@Set.mem_inter_iff];  simp[circle.points]; rw[dist_comm, Complex.dist_eq, Complex.abs_eq_sqrt_sq_add_sq, Complex.abs_eq_sqrt_sq_add_sq, ←@Mathlib.Tactic.RingNF.add_neg, ←@Mathlib.Tactic.RingNF.add_neg, @Complex.add_re, @Complex.add_im]; simp
  apply icc_M_inf M; unfold icc; rw [@Set.mem_setOf]; use c₀; constructor; exact hc₀; use c₁

-- Ludwigs wunderschöne Konstruktion
open Complex
/- lemma l_iff (M: Set ℂ)(z : ℂ)(l : line): x ∈ l.points ↔ ∃ t : ℝ, x = t * (l.z₁ + l.z₂) := by sorry
lemma l_pionts_iff (M: Set ℂ)(z : ℂ)(l₁ l₂ : line): l₁.points = l₂.points ↔ l₂.z₁ ∈ l₁.points ∧ l₂.z₂ ∈ l₁.points := by sorry

lemma sek_L_Minf (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1 ∈ M)(z₁ z₂ : ℂ)(hz1 : z₁ ∈ (M_inf M))(hz2 : z₂ ∈ (M_inf M))(l := {z₁ := I*z₁, z₂ := I*z₂}): l ∈ L (M_inf M) := by
  let c₁ : circle := {c := z₁, r := (dist z₁ z₂)}
  let c₂ : circle := {c := z₂, r := (dist z₁ z₂)}
  let x := c₁.points ∩ c₂.points
  have hc₁ : c₁ ∈ C (M_inf M) := by rw[c_in_C_M]; use z₁; use z₁; use z₂
  have hc₂ : c₂ ∈ C (M_inf M) := by rw[c_in_C_M]; use z₂; use z₁; use z₂
  have hx : x ⊆ icc (M_inf M) := by unfold icc; rw[Set.subset_def]; intro x hx ; rw [@Set.mem_setOf]; use c₁; constructor; exact hc₁; use c₂
  have hx : x ⊆ M_inf M := by apply le_trans; exact hx; apply icc_M_inf
  sorry
-/

lemma ir_M_inf (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1 ∈ M)(r : ℝ)(hr : ↑r ∈ (M_inf M)): Complex.I * r ∈ (M_inf M) := by
  let c₁ : circle := {c := 1, r := 2}
  let c₂ : circle := {c := -1, r := 2}
  let l : line := {z₁ := ⟨0,√3⟩ , z₂ := ⟨0,-√3⟩}
  let c : circle := {c := 0, r := |r|}
  have hc₁ : c₁ ∈ C (M_inf M) := by
    rw[c_in_C_M]; use 1; use -1; use 1;
    have h : dist (-1:ℂ) (1) = 2 := by simp[dist_comm,dist_eq,Complex.abs,one_add_one_eq_two];
    constructor; simp_all only [h];constructor; apply M_M_inf M h₁; constructor; apply z_neg_M_inf M h₀ (z:=1); apply M_M_inf M h₁; apply M_M_inf M h₁
  have hc₂ : c₂ ∈ C (M_inf M) := by
    rw[c_in_C_M]; use -1; use 1; use -1; have h : dist (1:ℂ) (-1) = 2 := by{simp[dist_eq,Complex.abs,one_add_one_eq_two]}; constructor; simp_all only [h];constructor; apply z_neg_M_inf M h₀ (z:=1); apply M_M_inf M h₁; constructor; apply M_M_inf M h₁; apply z_neg_M_inf M h₀ (z:=1); apply M_M_inf M h₁
  have hz₁: l.z₁ ∈ c₁.points := by simp[circle.points,Complex.abs_eq_sqrt_sq_add_sq]; ring_nf; rw [@Real.sqrt_eq_cases]; simp; ring
  have hz₂: l.z₂ ∈ c₁.points := by simp[circle.points,Complex.abs_eq_sqrt_sq_add_sq]; ring_nf; rw [@Real.sqrt_eq_cases]; simp; ring
  have hz₃: l.z₁ ∈ c₂.points := by simp[circle.points,Complex.abs_eq_sqrt_sq_add_sq]; ring_nf; rw [@Real.sqrt_eq_cases]; simp; ring
  have hz₄: l.z₂ ∈ c₂.points := by simp[circle.points,Complex.abs_eq_sqrt_sq_add_sq]; ring_nf; rw [@Real.sqrt_eq_cases]; simp; ring
  have hl: l ∈ L (M_inf M) := by unfold L; use l.z₁; use l.z₂; constructor; simp; constructor; apply icc_M_inf M; unfold icc; rw [@Set.mem_setOf]; use c₁; constructor; exact hc₁; use c₂; constructor; exact hc₂; rw [@Set.mem_inter_iff]; constructor; exact hz₁; exact hz₃; constructor; apply icc_M_inf M; unfold icc; rw [@Set.mem_setOf]; use c₁; constructor; exact hc₁; use c₂; constructor; exact hc₂; rw [@Set.mem_inter_iff]; constructor; exact hz₂; exact hz₄; simp
  have hc : c ∈ C (M_inf M) := by rw[c_in_C_M]; use 0; use 0; use r; constructor; simp_all only [dist_zero_left, Complex.norm_eq_abs, c]; simp; constructor; apply M_M_inf M h₀; constructor; apply M_M_inf M h₀; exact hr
  apply ilc_M_inf M; unfold ilc; rw [@Set.mem_setOf]; use c; constructor; exact hc; use l; constructor; exact hl; rw [@Set.mem_inter_iff]; constructor; simp[circle.points]; simp[line.points]; use (1/2 + r/(2 * (Real.sqrt 3))); norm_cast; rw[@Complex.ofReal_mul', @Complex.ofReal_mul']; ring_nf; simp[Complex.mk_eq_add_mul_I]; ring

lemma imath_M_inf (M: Set ℂ)(h₀: 0 ∈ M)(h₁: 1 ∈ M): Complex.I ∈ M_inf M := by
  rw[←mul_one I]; apply ir_M_inf M h₀ h₁ 1; apply M_M_inf M h₁
