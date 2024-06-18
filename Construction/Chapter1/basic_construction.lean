import Construction.Chapter1.set_MInf
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.MellinTransform

open  Construction
lemma z_neg_M_inf (M: Set ℂ) (h₀: (0:ℂ)∈ M) (z : ℂ) (hz : z ∈ (M_inf M)) : -z ∈ (M_inf M) := by
  by_cases z0:(z=0)
  . simp[z0]
    apply M_M_inf
    exact h₀
  let l : line := {z₁ := 0, z₂ := z}
  let c : Construction.circle := {c := 0, r := (dist 0 z)}
  have hl : l ∈ L (M_inf M) := by
    unfold L;
    use 0;
    use z;
    constructor;
    simp;
    constructor;
    . apply M_M_inf M h₀;
    constructor;
    . exact hz;
    . symm
      simp[z0]
  have hc : c ∈ C (M_inf M) := by
    rw[c_in_C_M]
    use 0
    use 0
    use z
    constructor
    . simp_all only [dist_zero_left, Complex.norm_eq_abs, l, c]
    constructor
    . apply M_M_inf M h₀
    constructor
    . apply M_M_inf M h₀
    exact hz
  have hlc : -z ∈ c.points ∩ l.points := by
    rw [Set.mem_inter_iff]
    constructor
    . simp[Construction.circle.points]
    simp[line.points]
    use 2
    push_cast
    ring_nf
  apply ilc_M_inf M
  unfold ilc
  rw [Set.mem_setOf]
  use c
  constructor
  . exact hc
  . use l

lemma add_M_Inf (M: Set ℂ) (h₀: (0:ℂ)∈ M) (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ (M_inf M)) (hz₂ : z₂ ∈ (M_inf M)):
     z₁ + z₂ ∈ (M_inf M) := by
  let c₁ : Construction.circle := {c := z₁, r := (dist 0 z₂)}
  let c₂ : Construction.circle := {c := z₂, r := (dist 0 z₁)}
  have hc₁ : c₁ ∈ C (M_inf M) := by
    rw[c_in_C_M]
    use z₁
    use 0
    use z₂
    constructor
    . simp_all only [dist_zero_left, Complex.norm_eq_abs, c₁]
    constructor
    . exact hz₁
    constructor
    . apply M_M_inf M h₀
    . exact hz₂
  have hc₂ : c₂ ∈ C (M_inf M) := by
    rw[c_in_C_M]
    use z₂
    use 0
    use z₁
    constructor
    . simp_all only [dist_zero_left, Complex.norm_eq_abs, c₂]
    constructor
    . exact hz₂
    constructor
    . apply M_M_inf M h₀
    . exact hz₁
  have hcc : z₁ + z₂ ∈ c₁.points ∩ c₂.points := by
    rw [Set.mem_inter_iff]
    simp[Construction.circle.points]
  apply icc_M_inf M
  unfold icc
  rw [Set.mem_setOf]
  use c₁
  constructor
  . exact hc₁
  use c₂

lemma sub_M_Inf (M: Set ℂ) (h₀: (0:ℂ)∈ M) (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ (M_inf M)) (hz₂ : z₂ ∈ (M_inf M)):
     z₁ - z₂ ∈ (M_inf M) := by
  have hz : z₁ - z₂ = z₁ + (-z₂) := by ring
  rw [hz]
  apply add_M_Inf M h₀ z₁ (-z₂) hz₁
  apply z_neg_M_inf M h₀ z₂ hz₂

lemma parallel_lines_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (z : ℂ) (hz: z ∈ (M_inf M)) (l₁: line)
    (hl₁ : l₁ ∈ L (M_inf M)): ∃ l₂, l₂ ∈ L (M_inf M) ∧ z ∈ l₂.points ∧ parallel l₁ l₂ := by
  let l₂ : line := {z₁ := z, z₂ := z-l₁.z₁+l₁.z₂}
  have hl₂ : l₂ ∈ L (M_inf M) := by
    unfold L
    use z
    use z-l₁.z₁+l₁.z₂
    constructor
    . simp
    constructor
    . exact hz
    constructor
    . apply add_M_Inf M h₀ (z-l₁.z₁) l₁.z₂
      apply sub_M_Inf M h₀ z l₁.z₁
      exact hz
      obtain ⟨q,_⟩ := (by apply l_in_L_M_imp (M_inf M) l₁; exact hl₁)
      exact q
      obtain ⟨_,t⟩ := (by apply l_in_L_M_imp (M_inf M) l₁; exact hl₁)
      exact t
    . refine Ne.intro ?_
      intro h
      rw[←sub_eq_iff_eq_add] at h
      simp at h
      have h': l₁.z₂ ≠  l₁.z₁ := by
        symm
        apply l_in_L_M_imp' (M_inf M) l₁
        exact hl₁
      contradiction
  use l₂
  constructor
  exact hl₂
  constructor
  . unfold line.points
    simp
    use 1
    simp
  . apply parallel_basis
    unfold line.z₁ line.z₂
    ring


lemma conj_M_Inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z : ℂ) (hz : z ∈ (M_inf M)):
  (starRingEnd ℂ) z ∈ (M_inf M) := by
  let c₀ : Construction.circle := {c := 0, r := (dist 0 z)}
  let c₁ : Construction.circle := {c := 1, r := (dist 1 z)}
  have hc₀ : c₀ ∈ C (M_inf M) := by
    rw[c_in_C_M]
    use 0
    use 0
    use z
    constructor
    . simp_all only [dist_zero_left, Complex.norm_eq_abs, c₀]
    constructor
    . apply M_M_inf M h₀
    constructor
    . apply M_M_inf M h₀
    exact hz
  have hc₁ : c₁ ∈ C (M_inf M) := by
    rw[c_in_C_M]
    use 1
    use 1
    use z
    constructor
    . simp_all only [dist_zero_left, Complex.norm_eq_abs, c₁]
    constructor
    . apply M_M_inf M h₁
    constructor
    . apply M_M_inf M h₁
    exact hz
  have hcc : (starRingEnd ℂ) z ∈ c₀.points ∩ c₁.points := by
    rw [Set.mem_inter_iff]
    simp[Construction.circle.points]
    rw[dist_comm, Complex.dist_eq, Complex.abs_eq_sqrt_sq_add_sq, Complex.abs_eq_sqrt_sq_add_sq,
    ←Mathlib.Tactic.RingNF.add_neg, ←Mathlib.Tactic.RingNF.add_neg, Complex.add_re, Complex.add_im]
    simp
  apply icc_M_inf M
  unfold icc
  rw [Set.mem_setOf]
  use c₀
  constructor
  . exact hc₀
  use c₁

open Complex

lemma ir_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (r : ℝ) (hr : ↑r ∈ (M_inf M)):
    Complex.I * r ∈ (M_inf M) := by
  let c₁ : Construction.circle := {c := 1, r := 2}
  let c₂ : Construction.circle := {c := -1, r := 2}
  let l : line := {z₁ := ⟨0,√3⟩ , z₂ := ⟨0,-√3⟩}
  let c : Construction.circle := {c := 0, r := |r|}
  have hc₁ : c₁ ∈ C (M_inf M) := by
    rw[c_in_C_M]
    use 1
    use -1
    use 1
    have h : dist (-1:ℂ) (1) = 2 := by
      simp[dist_comm,dist_eq,Complex.abs,one_add_one_eq_two]
    constructor
    . simp_all only [h]
    constructor
    . apply M_M_inf M h₁
    constructor
    . apply z_neg_M_inf M h₀ (z:=1)
      apply M_M_inf M h₁
    apply M_M_inf M h₁
  have hc₂ : c₂ ∈ C (M_inf M) := by
    rw[c_in_C_M]
    use -1
    use 1
    use -1
    have: dist (1:ℂ) (-1) = 2 := by
      simp[dist_eq,Complex.abs,one_add_one_eq_two]
    constructor
    . simp_all only [this]
    constructor
    . apply z_neg_M_inf M h₀ (z:=1)
      apply M_M_inf M h₁
    constructor
    . apply M_M_inf M h₁
    apply z_neg_M_inf M h₀ (z:=1)
    apply M_M_inf M h₁
  have hz₁: l.z₁ ∈ c₁.points := by
    simp[Construction.circle.points,Complex.abs_eq_sqrt_sq_add_sq]
    ring_nf
    rw [Real.sqrt_eq_cases]
    simp
    ring
  have hz₂: l.z₂ ∈ c₁.points := by
    simp[Construction.circle.points,Complex.abs_eq_sqrt_sq_add_sq]
    ring_nf
    rw [Real.sqrt_eq_cases]
    simp
    ring
  have hz₃: l.z₁ ∈ c₂.points := by
    simp[Construction.circle.points,Complex.abs_eq_sqrt_sq_add_sq]
    ring_nf
    rw [Real.sqrt_eq_cases]
    simp
    ring
  have hz₄: l.z₂ ∈ c₂.points := by
    simp[Construction.circle.points,Complex.abs_eq_sqrt_sq_add_sq]
    ring_nf
    rw [Real.sqrt_eq_cases]
    simp
    ring
  have hl: l ∈ L (M_inf M) := by
    unfold L
    use l.z₁
    use l.z₂
    constructor
    . simp
    constructor
    . apply icc_M_inf M
      unfold icc
      rw [Set.mem_setOf]
      use c₁
      constructor
      . exact hc₁
      use c₂
      constructor
      . exact hc₂
      rw [Set.mem_inter_iff]
      constructor
      . exact hz₁
      exact hz₃
    constructor
    . apply icc_M_inf M
      unfold icc
      rw [Set.mem_setOf]
      use c₁
      constructor
      . exact hc₁
      use c₂
      constructor
      . exact hc₂
      rw [Set.mem_inter_iff]
      constructor
      . exact hz₂
      exact hz₄
    simp
  have hc : c ∈ C (M_inf M) := by
    rw[c_in_C_M]
    use 0
    use 0
    use r
    constructor
    . simp_all only [dist_zero_left, Complex.norm_eq_abs, c]
      simp
    constructor
    . apply M_M_inf M h₀
    constructor
    . apply M_M_inf M h₀
    exact hr
  apply ilc_M_inf M
  unfold ilc
  rw [Set.mem_setOf]
  use c
  constructor
  . exact hc
  use l
  constructor
  . exact hl
  rw [Set.mem_inter_iff]
  constructor
  . simp[Construction.circle.points]
  simp[line.points]
  use (1/2 + r/(2 * (Real.sqrt 3)))
  norm_cast
  rw[Complex.ofReal_mul', Complex.ofReal_mul']
  ring_nf
  simp[Complex.mk_eq_add_mul_I]
  ring

lemma imath_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M): Complex.I ∈ M_inf M := by
  rw[←mul_one I]
  apply ir_M_inf M h₀ h₁ 1
  apply M_M_inf M h₁

lemma real_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ) (h: z ∈ M_inf M): ↑z.re ∈ M_inf M := by
  by_cases hreal: z.im = 0
  have hr: ∃ r : ℝ, r = z := by
    use z.re
    rw[Complex.ext_iff]
    simp
    symm
    exact hreal
  have hz: z = ↑(z.re) := by
    obtain ⟨r, hr⟩ := hr
    rw[←hr]
    simp
  rw[←hz]
  exact h
  let l : line := {z₁ := z, z₂ := starRingEnd ℂ z}
  let lr : line := {z₁ := 1, z₂ := 0}
  have hl : l ∈ L (M_inf M) := by
    unfold L
    use z
    use starRingEnd ℂ z
    constructor
    . simp
    constructor
    . exact h
    constructor
    . apply conj_M_Inf M h₀ h₁ z h
    by_contra h
    rw [ext_iff] at h
    simp at h
    contradiction
  have hlr : lr ∈ L (M_inf M) := by
    unfold L
    use 1
    use 0
    constructor
    . simp
    constructor
    . apply M_M_inf M h₁
    constructor
    . apply M_M_inf M h₀
    simp
  apply ill_M_inf M
  unfold ill
  rw [Set.mem_setOf]
  use l
  constructor
  . exact hl
  use lr
  constructor
  . exact hlr
  rw [Set.mem_inter_iff]
  constructor
  . simp[line.points]
    use 1/2
    refine ext_iff.mpr ?h.a
    simp
    ring_nf
    simp
  use z.re
  ring_nf

lemma i_z_imp_z_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℝ) (h: I * z ∈ M_inf M):
    ↑z ∈ M_inf M := by
  let lr : line := {z₁ := 1, z₂ := 0}
  let c : Construction.circle := {c := 0, r := dist 0 (I*z)}
  have hc : c ∈ C (M_inf M) := by
    rw[c_in_C_M]
    use 0
    use 0
    use I*z
    constructor
    . simp_all only [dist_zero_left, Complex.norm_eq_abs, c]
    constructor
    . apply M_M_inf M h₀
    constructor
    . apply M_M_inf M h₀
    exact h
  have hlr : lr ∈ L (M_inf M) := by
    unfold L
    use 1
    use 0
    constructor
    . simp
    constructor
    . apply M_M_inf M h₁
    constructor
    . apply M_M_inf M h₀
    simp
  apply ilc_M_inf M
  unfold ilc
  rw [Set.mem_setOf]
  use c
  constructor
  . exact hc
  use lr
  constructor
  . exact hlr
  rw [Set.mem_inter_iff]
  constructor
  . simp[Construction.circle.points]
  simp[line.points];

lemma im_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ) (h: z ∈ M_inf M): ↑z.im ∈ M_inf M := by
  let l : line := {z₁ := z, z₂ := z-1}
  let li : line := {z₁ := I, z₂ := 0}
  have hl : l ∈ L (M_inf M) := by
    unfold L
    use z
    use z-1
    constructor
    . simp
    constructor
    . exact h
    constructor
    . apply sub_M_Inf M h₀ z 1
      exact h
      apply M_M_inf M h₁
    exact Ne.symm (pred_ne_self z)
  have hlr : li ∈ L (M_inf M) := by
    unfold L
    use I
    use 0
    constructor
    . simp
    constructor
    . apply imath_M_inf M h₀ h₁
    constructor
    . apply M_M_inf M h₀
    simp
  have hi: I * z.im  ∈ M_inf M := by
    apply ill_M_inf M
    unfold ill
    rw [Set.mem_setOf]
    use l
    constructor
    . exact hl
    use li
    constructor
    . exact hlr
    rw [Set.mem_inter_iff]
    constructor
    . simp[line.points]
      use (1-z.re)
      ring_nf
      push_cast
      rw[← add_sub_assoc, Ring.add_left_neg, zero_sub, neg_add_eq_sub]
      refine sub_eq_of_eq_add' ?h.h
      rw[mul_comm]
      simp
    simp[line.points]
    use z.im
    ring
  apply i_z_imp_z_in_M_inf M h₀ h₁ z.im hi

lemma z_iff_re_im_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z: ℂ): z ∈ M_inf M ↔
    ↑z.re ∈ M_inf M ∧ ↑z.im ∈ M_inf M := by
  constructor
  . intro h
    constructor
    . apply real_in_M_inf M h₀ h₁ z h
    apply im_in_M_inf M h₀ h₁ z h
  intro h
  obtain ⟨hr, hi⟩ := h
  have hz: z = ↑z.re + ↑z.im * I := by simp
  rw[hz]
  apply add_M_Inf M h₀ ↑z.re (↑z.im * I)
  exact hr
  rw[mul_comm]
  apply ir_M_inf M h₀ h₁ z.im hi

--TODO: use parallel_lines_M_inf, because now we have it
lemma ab_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a b :ℝ) (ha: ↑a ∈ M_inf M) (hb: ↑b ∈ M_inf M):
    ↑(a * b) ∈ M_inf M := by
  let l₁ : line := {z₁ := a, z₂ := I}
  let l₂ : line := {z₁ := a+I*b-I, z₂ := I*b}
  let lr : line := {z₁ := 1, z₂ := 0}
  have _ : l₁ ∈ L (M_inf M) := by
    unfold L
    use a
    use I
    constructor
    . simp
    constructor
    . exact ha
    constructor
    . apply imath_M_inf M h₀ h₁
    by_contra h
    rw [ext_iff] at h
    simp at h
  have hl₂ : l₂ ∈ L (M_inf M) := by
    unfold L
    use (a+I*b-I)
    use I*b
    constructor
    . simp
    constructor
    . apply sub_M_Inf M h₀ (a+I*b) I
      apply add_M_Inf M h₀ a (I*b)
      exact ha
      exact ir_M_inf M h₀ h₁ b hb
      exact imath_M_inf M h₀ h₁
    constructor
    . exact ir_M_inf M h₀ h₁ b hb
    by_contra h
    rw [ext_iff] at h
    simp at h
  have hlr : lr ∈ L (M_inf M) := by
    unfold L
    use 1
    use 0
    constructor
    . simp
    constructor
    . apply M_M_inf M h₁
    constructor
    . apply M_M_inf M h₀
    simp
  apply ill_M_inf M
  unfold ill
  rw [Set.mem_setOf]
  use l₂
  constructor
  . exact hl₂
  use lr
  constructor
  . exact hlr
  rw [Set.mem_inter_iff]
  constructor
  . simp[line.points]
    use b
    ring
  use a*b
  ring

lemma mul_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a b :ℂ ) (ha: a ∈ M_inf M) (hb: b ∈ M_inf M): a * b ∈ M_inf M:= by
  refine (z_iff_re_im_M_inf M h₀ h₁ (a * b)).mpr ?_
  constructor
  simp
  apply sub_M_Inf M h₀
  norm_cast
  apply ab_in_M_inf M h₀ h₁
  exact real_in_M_inf M h₀ h₁ a ha
  exact real_in_M_inf M h₀ h₁ b hb
  norm_cast
  apply ab_in_M_inf M h₀ h₁
  exact im_in_M_inf M h₀ h₁ a ha
  exact im_in_M_inf M h₀ h₁ b hb
  simp
  apply add_M_Inf M h₀
  norm_cast
  apply ab_in_M_inf M h₀ h₁
  exact real_in_M_inf M h₀ h₁ a ha
  exact im_in_M_inf M h₀ h₁ b hb
  norm_cast
  apply ab_in_M_inf M h₀ h₁
  exact im_in_M_inf M h₀ h₁ a ha
  exact real_in_M_inf M h₀ h₁ b hb

lemma ainv_in_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a :ℝ) (ha: ↑a ∈ M_inf M): ↑(a⁻¹) ∈ M_inf M := by
  by_cases h: a = 0
  . rw[h]
    apply M_M_inf
    simp
    exact h₀
  rw[←ne_eq] at h
  let l: line := {z₁ := 1-I*a+I, z₂ := I}
  let lr : line := {z₁ := 1, z₂ := 0}
  have hl : l ∈ L (M_inf M) := by
    unfold L
    use (1-I*a+I)
    use I
    constructor
    . simp
    constructor
    . apply add_M_Inf M h₀ (1-I*a) I
      apply sub_M_Inf M h₀ 1 (I*a)
      exact M_M_inf M h₁
      exact ir_M_inf M h₀ h₁ a ha
      exact imath_M_inf M h₀ h₁
    constructor
    . exact imath_M_inf M h₀ h₁
    by_contra h
    rw [ext_iff] at h
    simp at h
  have hlr : lr ∈ L (M_inf M) := by
    unfold L
    use 1
    use 0
    constructor
    . simp
    constructor
    . apply M_M_inf M h₁
    constructor
    . apply M_M_inf M h₀
    simp
  apply ill_M_inf M
  unfold ill
  rw [Set.mem_setOf]
  use l
  constructor
  . exact hl
  use lr
  constructor
  . exact hlr
  rw [Set.mem_inter_iff]
  constructor
  . simp[line.points]
    use a⁻¹
    ring_nf
    rw [mul_rotate]
    simp[*]
  simp[line.points]
  use a⁻¹
  norm_cast

-- Helper lemma for the next lemma
lemma z_inv_eq (z:ℂ) (hz: z ≠ 0): z⁻¹ = z.re / (z.re^2+z.im^2)-(z.im/ (z.re^2+z.im^2) )*I:= by
   calc z⁻¹ = 1/ z := by simp
  _ = (starRingEnd ℂ z /  starRingEnd ℂ z)*(1/z) := by
      rw[div_self,one_mul]
      simp_all only [ne_eq, map_eq_zero, not_false_eq_true]
  _ = (starRingEnd ℂ z /  (starRingEnd ℂ z * z)) := by rw [← div_mul_eq_div_mul_one_div]
  _ = (starRingEnd ℂ z /  Complex.normSq z) := by rw[mul_comm, Complex.mul_conj z]
  _ = (starRingEnd ℂ z /  (z.re^2+z.im^2)) := by
      rw[Complex.normSq_apply]
      norm_cast
      rw[pow_two, pow_two]
  _ = ((z.re - z.im *I)/ (z.re^2+z.im^2) ) := by
    have h: starRingEnd ℂ z = z.re - z.im *I := by
      refine ((fun {z w} ↦ ext_iff.mpr) ?_).symm
      constructor
      simp
      simp
    rw[h]
  _ = z.re / (z.re^2+z.im^2)-(z.im/ (z.re^2+z.im^2) )*I := by rw [←div_sub_div_same, mul_div_right_comm]


lemma inv_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (a :ℂ ) (ha: a ∈ M_inf M): a⁻¹ ∈ M_inf M:= by
  by_cases h: a = 0
  . rw[h]
    apply M_M_inf
    simp
    exact h₀;
  rw[←ne_eq] at h;rw[z_inv_eq _ h]
  refine sub_M_Inf M h₀ (↑a.re / (↑a.re ^ 2 + ↑a.im ^ 2)) (↑a.im / (↑a.re ^ 2 + ↑a.im ^ 2) * I) ?_ ?_
  rw[ Field.div_eq_mul_inv]
  apply mul_M_inf M h₀ h₁ (↑a.re) (↑a.re ^ 2 + ↑a.im ^ 2)⁻¹ ?_ ?_
  exact real_in_M_inf M h₀ h₁ a ha
  norm_cast
  apply ainv_in_M_inf M h₀ h₁
  push_cast
  apply add_M_Inf M h₀ (↑a.re ^ 2) (↑a.im ^ 2)
  rw[pow_two]
  apply mul_M_inf M h₀ h₁ (↑a.re) (↑a.re) (by apply real_in_M_inf M h₀ h₁; exact ha)
    (by apply real_in_M_inf M h₀ h₁; exact ha)
  rw[pow_two]
  apply mul_M_inf M h₀ h₁ (↑a.im) (↑a.im) (by apply im_in_M_inf M h₀ h₁; exact ha)
    (by apply im_in_M_inf M h₀ h₁; exact ha)
  apply mul_M_inf M h₀ h₁ _ _ ?_ (by exact imath_M_inf M h₀ h₁)
  rw[ Field.div_eq_mul_inv]
  apply mul_M_inf M h₀ h₁ _ _ (by exact im_in_M_inf M h₀ h₁ a ha)
  norm_cast
  apply ainv_in_M_inf M h₀ h₁
  push_cast
  apply add_M_Inf M h₀ (↑a.re ^ 2) (↑a.im ^ 2)
  rw[pow_two]
  apply mul_M_inf M h₀ h₁ (↑a.re) (↑a.re) (by apply real_in_M_inf M h₀ h₁; exact ha)
    (by apply real_in_M_inf M h₀ h₁; exact ha)
  rw[pow_two]
  apply mul_M_inf M h₀ h₁ (↑a.im) (↑a.im) (by apply im_in_M_inf M h₀ h₁; exact ha)
    (by apply im_in_M_inf M h₀ h₁; exact ha)

lemma root_cast (x: ℝ) (h: x ≥ 0): ↑((x:ℝ) ^ (1/2:ℝ)) = (x:ℂ) ^ (1/2:ℂ) := by
  sorry

lemma inv_comp_root (r:ℝ) (h: 0 < r): ↑r ^ (1 / 2:ℂ ) = ((1 / (r:ℂ) )^ (1 / 2:ℂ))⁻¹:= by
  nth_rewrite 2 [one_div]
  rw[←cpow_neg, inv_cpow, ←cpow_neg, neg_neg]
  rw[arg_ofReal_of_nonneg ]
  . symm
    exact Real.pi_ne_zero
  apply le_of_lt h

/- lemma root_copmlex (z : ℂ): z ^ (1/2:ℂ) = (((abs z)+z.re)/2)^ (1/2:ℂ)+I*z.im/|z.im| *
    (((abs z )-z.re)/2)^ (1/2:ℂ) := by sorry -/

lemma point_in_circle_pythagorean (z: ℂ) (c: Construction.circle) (hr: 0 < c.r): z ∈ c.points ↔ (dist c.c.re z.re)^2 + (dist c.c.im z.im)^2 = c.r^2 := by
  simp only [Construction.circle.points, Set.mem_setOf_eq, mem_sphere_iff_norm, norm_eq_abs]
  rw[←dist_eq]
  constructor
  . intro h
    rw [← h, dist_eq, Real.dist_eq, Real.dist_eq, Complex.sq_abs, normSq_apply]
    norm_cast
    rw[pow_two, pow_two, abs_sub_sq, abs_sub_sq, sub_re, sub_im,←sub_eq_zero, ←sub_sub, one_add_one_eq_two]
    ring
  . intro h
    rw [←abs_of_pos hr, ←abs_dist,←sq_eq_sq_iff_abs_eq_abs, ← h]
    rw[dist_eq, Real.dist_eq, Real.dist_eq, Complex.sq_abs, normSq_apply, ←sub_eq_zero,  sub_re, sub_im, pow_two, pow_two, abs_sub_sq, abs_sub_sq]
    ring_nf

lemma one_real_root (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (r : ℝ) (hr: ↑r ∈ M_inf M) (hr': r ≥ 1):
    (r:ℂ) ^ (1/2:ℂ)  ∈ M_inf M := by
  let c₁ : Construction.circle := {c := r/2, r := |r|/2}
  let l : line := {z₁ := 1, z₂ := I + 1}
  let c : Construction.circle := {c := 0, r := dist (0:ℂ) ((r:ℂ) ^ (1/2:ℂ))}
  let lr : line := {z₁ := 1, z₂ := 0 }
  have hc₁ : c₁ ∈ C (M_inf M) := by
    rw[c_in_C_M]
    use (r/2)
    use (0)
    use (r/2)
    constructor
    . simp only [dist_zero_left, norm_div, norm_eq_abs, abs_ofReal, RCLike.norm_ofNat]
    constructor
    . rw[div_eq_mul_inv]
      apply mul_M_inf M h₀ h₁
      exact hr
      apply inv_M_inf M h₀ h₁
      rw[←one_add_one_eq_two]
      apply add_M_Inf M h₀ 1 1
      apply M_M_inf M h₁
      apply M_M_inf M h₁
    constructor
    . apply M_M_inf M h₀
    rw[div_eq_mul_inv]
    apply mul_M_inf M h₀ h₁
    exact hr
    apply inv_M_inf M h₀ h₁
    rw[←one_add_one_eq_two]
    apply add_M_Inf M h₀ 1 1
    apply M_M_inf M h₁
    apply M_M_inf M h₁
  have hl : l ∈ L (M_inf M) := by
    unfold L
    use 1
    use I + 1
    constructor
    . simp
    constructor
    . apply M_M_inf M h₁
    constructor
    . apply add_M_Inf M h₀
      apply imath_M_inf M h₀ h₁
      apply M_M_inf M h₁
    simp
  have hlr : lr ∈ L (M_inf M) := by
    unfold L
    use 1
    use 0
    constructor
    . simp
    constructor
    . apply M_M_inf M h₁
    constructor
    . apply M_M_inf M h₀
    simp
  let x : ℂ := 1 + I * (r-1)^(1/2:ℂ)
  have hx : 1 + I * (r-1)^(1/2:ℂ) ∈ M_inf M := by
    apply ilc_M_inf M
    unfold ilc
    rw [Set.mem_setOf]
    use c₁
    constructor
    . exact hc₁
    use l
    constructor
    . exact hl
    rw [Set.mem_inter_iff]
    constructor
    . rw[point_in_circle_pythagorean]
      simp only [div_ofNat_re, ofReal_re, add_re, one_re, mul_re, I_re, zero_mul, I_im,
        one_mul, zero_sub, Real.dist_eq, _root_.sq_abs, div_ofNat_im, ofReal_im, zero_div, add_im,
        one_im, mul_im, zero_add, abs_neg, div_pow]
      norm_cast
      rw[←root_cast,ofReal_im, ofReal_re]
      push_cast
      have : 0 ≤ r-1  := by linarith
      nth_rewrite 2 [←Real.rpow_natCast]
      push_cast
      rw[←Real.rpow_mul (this) (1/2) 2,one_div_mul_eq_div, div_self, Real.rpow_one, neg_zero,
        add_zero, sub_sq (r/2) 1]
      ring
      exact Ne.symm (NeZero.ne' 2)
      linarith
      simp only [gt_iff_lt, Nat.ofNat_pos, div_pos_iff_of_pos_right, abs_pos, ne_eq]
      linarith
    simp only [line.points, mul_one, Set.mem_setOf_eq]
    use 1 - (r-1)^(1/2:ℝ)
    ring_nf
    push_cast
    rw [root_cast]
    ring_nf
    rw[mul_comm]
    simp only [ofReal_add, ofReal_neg, ofReal_one, one_div]
    rw [neg_add_eq_sub, ge_iff_le, le_tsub_iff_left, add_zero]
    exact hr'
    exact hr'
  have hx' : dist 0 x =  dist (0:ℂ) ((r:ℂ) ^ (1/2:ℂ) ) := by
    nth_rewrite 2 [←abs_dist]
    rw[←abs_dist,←sq_eq_sq_iff_abs_eq_abs, dist_eq, dist_eq, Complex.sq_abs, Complex.sq_abs,
      normSq_apply, normSq_apply, ←sub_eq_zero, sub_re, sub_im, sub_re, sub_im, zero_re,
      zero_im, zero_sub, zero_sub, zero_sub, zero_sub, ←root_cast, ofReal_re, ofReal_im,
      neg_zero, mul_zero, add_zero, ←pow_two, ←pow_two, ←pow_two]
    nth_rewrite 3 [neg_eq_neg_one_mul, pow_two]
    rw[←mul_assoc]
    nth_rewrite 2 [mul_comm]
    rw[←mul_assoc, ←neg_eq_neg_one_mul, neg_neg, one_mul, ←pow_two]
    nth_rewrite 3 [←Real.rpow_natCast]
    push_cast
    rw[←Real.rpow_mul, one_div_mul_eq_div, div_self, Real.rpow_one]
    ring_nf
    simp only [add_re, one_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, add_im,
      one_im, mul_im, zero_add]
    norm_cast
    rw[←root_cast, ofReal_im, ofReal_re]
    simp only [neg_zero, add_zero, one_pow, Int.reduceNegSucc, Int.cast_neg, Int.cast_one]
    nth_rewrite 1 [←Real.rpow_natCast]
    push_cast
    rw[←Real.rpow_mul, one_div_mul_eq_div, div_self, Real.rpow_one]
    simp only [add_sub_cancel_right, add_right_neg]
    . simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    . linarith
    . rw [@Int.cast_negSucc, zero_add]
      push_cast
      linarith
    . simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    . linarith
    . linarith
  have hc₁ : c ∈ C (M_inf M) := by
    rw[c_in_C_M]
    use 0
    use 0
    use x
    constructor
    . rw[hx']
    constructor
    . apply M_M_inf M h₀
    constructor
    . apply M_M_inf M h₀
    exact hx
  apply ilc_M_inf M
  unfold ilc
  rw [Set.mem_setOf]
  use c
  constructor
  . exact hc₁
  use lr
  constructor
  . exact hlr
  rw [Set.mem_inter_iff]
  constructor
  . simp[Construction.circle.points]
  simp[line.points]
  use r ^ (1/2:ℝ)
  ring_nf
  rw [root_cast]
  apply ge_trans (b:=1) hr' (by simp)


lemma zero_real_root_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (r : ℝ ) (hr: ↑r ∈ M_inf M) (hr': r ≥ 0):
    (r:ℂ) ^ (1/2:ℂ) ∈ M_inf M := by
  by_cases h: r > 0
  . by_cases hinv: r ≥ 1
    . exact one_real_root M h₀ h₁ r hr hinv
    . rw [inv_comp_root r h]
      apply inv_M_inf M h₀ h₁
      norm_cast
      apply one_real_root M h₀ h₁ (1 / r)
      push_cast
      rw [div_eq_mul_inv, one_mul]
      apply inv_M_inf M h₀ h₁
      exact hr
      rw [one_div, ge_iff_le, le_inv, inv_one]
      rw [not_le] at hinv
      simp only [le_of_lt, hinv]
      exact zero_lt_one
      exact h
  . have: r = 0 := by linarith
    rw[this]
    apply M_M_inf
    simp
    exact h₀

    /-. have g: 0 < -r := by
        rw [@Right.neg_pos_iff, lt_iff_le_and_ne]
        constructor
        . rw [Mathlib.Tactic.PushNeg.not_gt_eq] at h
          exact h
        . exact zero
       by_cases hinv: (-r) ≥ 1
      . rw[neg_comp_root r] --!not True
        apply mul_M_inf M h₀ h₁ (↑(-r) ^ (1 / 2)) I
        apply one_real_root M h₀ h₁ (-r) (by push_cast; apply z_neg_M_inf M h₀; exact hr ) hinv
        apply imath_M_inf M h₀ h₁
      . rw[neg_comp_root r] --!not True
        rw [inv_comp_root (-r)]
        apply mul_M_inf M h₀ h₁
        apply inv_M_inf M h₀ h₁
        norm_cast
        apply one_real_root M h₀ h₁ (1 / -r)
        push_cast
        rw [div_eq_mul_inv, one_mul]
        apply inv_M_inf M h₀ h₁
        apply z_neg_M_inf M h₀
        exact hr
        rw [one_div, ge_iff_le, le_inv, inv_one]
        rw [not_le] at hinv
        simp only [le_of_lt, hinv]
        exact zero_lt_one
        exact g
        apply imath_M_inf M h₀ h₁
        exact g
 -/

lemma abs_M_Inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z : ℂ) (hz: z ∈ M_inf M):
    ↑(abs z) ∈ M_inf M := by
  have: (abs z:ℂ) = (z.re^2+z.im^2)^(1/2:ℂ) := by
    rw [abs_eq_sqrt_sq_add_sq, Real.sqrt_eq_rpow, root_cast]
    simp only [ofReal_add, ofReal_pow, one_div]
    nth_rewrite 2 [←abs_sq]
    rw [←abs_sq]
    apply ge_trans (b:=|z.re^2+z.im^2|) (by exact abs_add (z.re ^ 2) (z.im ^ 2)) (by simp)
  rw[this]
  norm_cast
  apply zero_real_root_M_inf M h₀ h₁ _ _ (add_nonneg (pow_two_nonneg z.re) (pow_two_nonneg z.im))
  push_cast
  apply add_M_Inf M h₀
  rw [sq]
  apply mul_M_inf M h₀ h₁
  apply real_in_M_inf M h₀ h₁
  exact hz
  apply real_in_M_inf M h₀ h₁
  exact hz
  rw [sq]
  apply mul_M_inf M h₀ h₁
  apply im_in_M_inf M h₀ h₁
  exact hz
  apply im_in_M_inf M h₀ h₁
  exact hz


lemma rabs_M_Inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (r : ℝ) (hr: ↑r ∈ M_inf M):
    ↑|r| ∈ M_inf M := by
  by_cases h: r ≥ 0
  . have h': ↑|r| = r := by simp[h]
    rw[h']
    apply real_in_M_inf M h₀ h₁ r hr
  . have h': ↑|r| = -r := by simp_all [h, le_of_lt]
    rw[h']
    push_cast
    apply z_neg_M_inf M h₀ r hr


lemma root_M_inf (M: Set ℂ) (h₀: 0 ∈ M) (h₁: 1 ∈ M) (z : ℂ) (hz: z ∈ M_inf M):
    z ^ (1/2:ℂ) ∈ M_inf M := by
    sorry

--It is nicer to yous polar coordinates
  /- rw[root_copmlex]
  apply add_M_Inf M h₀
  norm_cast
  apply real_root_M_inf M h₀ h₁
  push_cast
  rw [div_eq_mul_inv]
  apply mul_M_inf M h₀ h₁
  apply add_M_Inf M h₀
  apply abs_M_Inf M h₀ h₁
  exact hz
  apply real_in_M_inf M h₀ h₁
  exact hz
  apply inv_M_inf M h₀ h₁
  rw [←one_add_one_eq_two]
  apply add_M_Inf M h₀ 1 1
  apply M_M_inf M h₁
  apply M_M_inf M h₁
  apply mul_M_inf M h₀ h₁
  rw [div_eq_mul_inv]
  apply mul_M_inf M h₀ h₁
  apply mul_M_inf M h₀ h₁
  apply imath_M_inf M h₀ h₁
  apply im_in_M_inf M h₀ h₁
  exact hz
  apply inv_M_inf M h₀ h₁
  apply rabs_M_Inf M h₀ h₁
  apply im_in_M_inf M h₀ h₁
  exact hz
  norm_cast
  apply real_root_M_inf M h₀ h₁
  push_cast
  rw [div_eq_mul_inv]
  apply mul_M_inf M h₀ h₁
  apply sub_M_Inf M h₀
  apply abs_M_Inf M h₀ h₁
  exact hz
  apply real_in_M_inf M h₀ h₁
  exact hz
  apply inv_M_inf M h₀ h₁
  rw [←one_add_one_eq_two]
  apply add_M_Inf M h₀ 1 1
  apply M_M_inf M h₁
  apply M_M_inf M h₁ -/

example (a b : ℝ): a ≤ b ∧ a ≠ b → a < b := by
  rw [← lt_iff_le_and_ne]; exact id

example (a b :ℂ ): dist a b = |dist a b| := by rw [@abs_dist]

example ( a b : ℝ ) (ha: 0 ≤ a) (hb: 0 ≤ b): 0 ≤ a + b := by
  exact add_nonneg ha hb
