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


lemma c_in_C_M (N:Set ℂ): c ∈ C N ↔  ∃ z r₁ r₂, c = {c:=z, r:=(dist r₁ r₂)} ∧ z ∈ N ∧ r₁ ∈ N ∧ r₂ ∈ N := by
  unfold C; simp


def ill (M:Set ℂ): Set ℂ := { z  |∃l₁ ∈ L M, ∃ l₂ ∈ L M,  z ∈ l₁.points ∩ l₂.points}
def ilc (M:Set ℂ): Set ℂ := { z  |∃c ∈ C M, ∃ l ∈ L M,  z ∈ c.points ∩ l.points}
def icc (M:Set ℂ): Set ℂ := { z  |∃c₁ ∈ C M, ∃ c₂ ∈ C M,  z ∈ c₁.points ∩ c₂.points}


def Z_M (M : Set ℂ) : Set ℂ := M ∪ ill M ∪ ilc M ∪ icc M

def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => Z_M (M_I M n)

def M_inf (M : Set ℂ) : Set ℂ :=  ⋃ (n : ℕ), M_I M n

lemma M_in_Z_M (M : Set ℂ) : M ⊆ Z_M M := by
  unfold Z_M; intro x; intro hx; left; left; left; exact hx

lemma M_I_Monotone (M : Set ℂ) : ∀n, M_I M n ⊆ M_I M (n+1) := by
  intro n; apply M_in_Z_M

lemma M_I_Monotone_elm (M : Set ℂ)(n : ℕ) : ∀ x, x ∈ M_I M n → x ∈ M_I M (Nat.succ n) := by
  intro n; apply M_in_Z_M

lemma M_in_M_I (M : Set ℂ) : ∀n, M ⊆ M_I M n := by
  intro n; induction n; simp [M_I]; exact fun ⦃a⦄ a => a;
  case succ n hn => apply le_trans hn; apply M_I_Monotone

lemma M_I_Monotone' (M : Set ℂ)(n m : ℕ)(h: n ≤ m) :  M_I M n ⊆ M_I M m := by
  apply monotone_nat_of_le_succ; apply M_I_Monotone; exact h

lemma M_I_Monotone_elm' (M : Set ℂ)(n m : ℕ)(h: n ≤ m) : ∀ x, x ∈ M_I M n → x ∈ M_I M m := by
  intro x; apply M_I_Monotone' M n m h

lemma M_I_in_M_inf (M : Set ℂ)(m: ℕ): M_I M m ⊆ M_inf M := by
  unfold M_inf; exact Set.subset_iUnion_of_subset m fun ⦃a⦄ a => a

lemma M_I_in_M_inf' (M : Set ℂ)(x : ℂ)(m: ℕ) :  x ∈ M_I M m → x ∈  M_inf M := by
  apply M_I_in_M_inf

lemma M_M_inf (M : Set ℂ) : M ⊆ M_inf M := by apply le_trans (M_in_M_I M 0) (M_I_in_M_inf M 0)

lemma M_M_inf' (M : Set ℂ)(x : ℂ) : x ∈ M → x ∈ M_inf M := by
  apply M_M_inf

/- lemma M_inf_in_M_I (M : Set ℂ) : ∀ x ∈ M_inf M, ∃ n, ↑x ∈ (M_I M n):= by
  intro x; apply Set.mem_iUnion.mp
 -/
lemma M_inf_in_M_I (M : Set ℂ)(x:ℂ): x ∈ M_inf M ↔ ∃ n, x ∈ (M_I M n):= by
  apply Set.mem_iUnion

lemma M_inf_in_M_I' (M : Set ℂ)(x:ℂ): x ∈ M_inf M ↔ ∀ᶠ n in Filter.atTop, x ∈ M_I M n := by
  simp; constructor; intro h; have hn: ∃ n, x ∈ M_I M n := by exact (M_inf_in_M_I M x).mp h
  obtain ⟨n, hn⟩ := hn; use n; intro m hm; apply M_I_Monotone_elm' M n m hm; exact hn
  simp; intro n hn; apply M_I_in_M_inf' M x n; apply hn; simp

-- TODO: Show if needed
structure M where
  (M : Set ℂ)
  (M_0 : ↑(0:ℂ)  ∈ ↑M)
  (M_1 : 1 ∈ M)

lemma L_M_inf_iff_M_N (N: Set ℂ): l ∈ L (M_inf N) ↔ ∀ᶠ n in Filter.atTop, l ∈ L (M_I N n) := by
  unfold L; simp; constructor; intro h; obtain ⟨z₁, z₂, h, hz₁, hz₂⟩ := h; rw[M_inf_in_M_I'] at hz₁ hz₂;
  rw [←@Filter.eventually_atTop]; filter_upwards [hz₁, hz₂]; rw [h]; simp; intro a hz₁a hz₂a; use z₁; use z₂;
  intro h; obtain ⟨n, hn⟩ := h; have h: ∃ z₁ z₂, l = {z₁ := z₁, z₂ := z₂} ∧ z₁ ∈ M_I N n ∧ z₂ ∈ M_I N n := by apply hn; simp
  obtain ⟨z₁, z₂, h, hz₁, hz₂⟩ := h; use z₁; use z₂; rw [h]; simp; constructor;
  exact M_I_in_M_inf' N z₁ n hz₁; exact M_I_in_M_inf' N z₂ n hz₂

lemma C_M_inf_iff_M_N (N: Set ℂ): c ∈ C (M_inf N) ↔ ∀ᶠ n in Filter.atTop, c ∈ C (M_I N n) := by
  unfold C; simp; constructor; intro h; obtain ⟨z, r₁, r₂, h, hz, hr₁, hr₂⟩ := h; rw[M_inf_in_M_I'] at hz hr₁ hr₂;
  rw [←@Filter.eventually_atTop]; filter_upwards [hz, hr₁, hr₂]; rw [h]; simp; intro a hza hr₁a hr₂a; use z; use r₁; use r₂;
  intro h; obtain ⟨n, hn⟩ := h; have h: ∃ z r₁ r₂, c = {c:=z, r:=(dist r₁ r₂)} ∧ z ∈ M_I N n ∧ r₁ ∈ M_I N n ∧ r₂ ∈ M_I N n := by apply hn; simp
  obtain ⟨z, r₁, r₂, h, hz, hr₁, hr₂⟩ := h; use z; use r₁; use r₂; rw [h]; simp; constructor;
  exact M_I_in_M_inf' N z n hz; constructor; exact M_I_in_M_inf' N r₁ n hr₁; exact M_I_in_M_inf' N r₂ n hr₂

lemma ill_M_inf (N: Set ℂ): ill (M_inf N) ⊆ M_inf N := by
  intro z; intro hz; unfold ill at hz; rw [@Set.mem_setOf] at hz; obtain ⟨l₁, hl₁, l₂, hl₂, hz⟩ := hz;
  rw [L_M_inf_iff_M_N] at hl₁ hl₂; have zILL : ∃ n, z ∈ ill (M_I N n) := by {
    unfold ill; simp[exists_comm.mp]; simp at hl₁ hl₂; obtain ⟨a₁, hl₁⟩ := hl₁; obtain ⟨a₂, hl₂⟩ := hl₂;let n := max a₁ a₂; use n; use l₁; refine
      exists_and_left.mp ?h.a; use l₂; constructor; apply hl₁; simp_all only [Set.mem_inter_iff, le_max_iff, le_refl, true_or, n]; constructor; apply hl₂; simp_all only [Set.mem_inter_iff, le_max_iff, le_refl, or_true, n]; simp_all only [Set.mem_inter_iff, and_self]}
  obtain ⟨n, hzn⟩ := zILL; apply M_I_in_M_inf' N z n.succ; unfold M_I Z_M;
  simp_all only [Filter.eventually_atTop, ge_iff_le, Set.mem_inter_iff, Set.mem_union, or_true, true_or]

lemma ilc_M_inf (N: Set ℂ): ilc (M_inf N) ⊆ M_inf N := by
  intro z; intro hz; unfold ilc at hz; rw [@Set.mem_setOf] at hz; obtain ⟨c, hc, l, hl, hz⟩ := hz;
  rw [C_M_inf_iff_M_N] at hc; rw [L_M_inf_iff_M_N] at hl; have zILC : ∃ n, z ∈ ilc (M_I N n) := by {
    unfold ilc; simp[exists_comm.mp]; simp at hc hl; obtain ⟨a₁, hc⟩ := hc; obtain ⟨a₂, hl⟩ := hl;let n := max a₁ a₂; use n; use c; refine
      exists_and_left.mp ?h.a; use l; constructor; apply hc; simp_all only [Set.mem_inter_iff, le_max_iff, le_refl, true_or, n]; constructor; apply hl; simp_all only [Set.mem_inter_iff, le_max_iff, le_refl, or_true, n]; simp_all only [Set.mem_inter_iff, and_self]}
  obtain ⟨n, hzn⟩ := zILC; apply M_I_in_M_inf' N z n.succ; unfold M_I Z_M;
  simp_all only [Filter.eventually_atTop, ge_iff_le, Set.mem_inter_iff, Set.mem_union, or_true, true_or]

lemma icc_M_inf (N: Set ℂ): icc (M_inf N) ⊆ M_inf N := by
  intro z; intro hz; unfold icc at hz; rw [@Set.mem_setOf] at hz; obtain ⟨c₁, hc₁, c₂, hc₂, hz⟩ := hz;
  rw [C_M_inf_iff_M_N] at hc₁ hc₂; have zICC : ∃ n, z ∈ icc (M_I N n) := by {
    unfold icc; simp[exists_comm.mp]; simp at hc₁ hc₂; obtain ⟨a₁, hc₁⟩ := hc₁; obtain ⟨a₂, hc₂⟩ := hc₂;let n := max a₁ a₂; use n; use c₁; refine
      exists_and_left.mp ?h.a; use c₂; constructor; apply hc₁; simp_all only [Set.mem_inter_iff, le_max_iff, le_refl, true_or, n]; constructor; apply hc₂; simp_all only [Set.mem_inter_iff, le_max_iff, le_refl, or_true, n]; simp_all only [Set.mem_inter_iff, and_self]}
  obtain ⟨n, hzn⟩ := zICC; apply M_I_in_M_inf' N z n.succ; unfold M_I Z_M;
  simp_all only [Filter.eventually_atTop, ge_iff_le, Set.mem_inter_iff, Set.mem_union, or_true, true_or]

--(h₁: 1 ∈ N)
lemma z_neg_M_inf (N: Set ℂ)(h₀: (0:ℂ)∈ N)(z : ℂ)(hz : z ∈ (M_inf N)) : -z ∈ (M_inf N) := by
  let l : line := {z₁ := 0, z₂ := z}
  let c : circle := {c := 0, r := (dist 0 z)}
  have hl : l ∈ L (M_inf N) := by unfold L; use 0; use z; constructor; simp; constructor; apply M_M_inf' N 0 h₀; exact hz
  have hc : c ∈ C (M_inf N) := by rw[c_in_C_M]; use 0; use 0; use z; constructor; simp_all only [dist_zero_left, Complex.norm_eq_abs, l, c]; constructor; apply M_M_inf' N 0 h₀; constructor; apply M_M_inf' N 0 h₀; exact hz
  have hlc : -z ∈ c.points ∩ l.points := by {rw [@Set.mem_inter_iff]; constructor; simp[circle.points]; simp[line.points]; use 2; ring_nf; calc  -(2 * z) + z = -z := by ring}
  apply ilc_M_inf N; unfold ilc; rw [@Set.mem_setOf]; use c; constructor; exact hc ; use l

lemma add_M_Inf (N: Set ℂ)(h₀: (0:ℂ)∈ N)(z₁ z₂ : ℂ)(hz₁ : z₁ ∈ (M_inf N))(hz₂ : z₂ ∈ (M_inf N)): z₁ + z₂ ∈ (M_inf N) := by
  let c₁ : circle := {c := z₁, r := (dist 0 z₂)}
  let c₂ : circle := {c := z₂, r := (dist 0 z₁)}
  have hc₁ : c₁ ∈ C (M_inf N) := by rw[c_in_C_M]; use z₁; use 0; use z₂; constructor; simp_all only [dist_zero_left, Complex.norm_eq_abs, c₁]; constructor; exact hz₁; constructor; apply M_M_inf' N 0 h₀; exact hz₂
  have hc₂ : c₂ ∈ C (M_inf N) := by rw[c_in_C_M]; use z₂; use 0; use z₁; constructor; simp_all only [dist_zero_left, Complex.norm_eq_abs, c₂]; constructor; exact hz₂; constructor; apply M_M_inf' N 0 h₀; exact hz₁
  have hcc : z₁ + z₂ ∈ c₁.points ∩ c₂.points := by rw [@Set.mem_inter_iff];  simp[circle.points]
  apply icc_M_inf N; unfold icc; rw [@Set.mem_setOf]; use c₁; constructor; exact hc₁; use c₂

lemma conj_M_Inf (N: Set ℂ)(h₀: 0 ∈ N)(h₁: 1 ∈ N)(z : ℂ)(hz : z ∈ (M_inf N)): (starRingEnd ℂ) z ∈ (M_inf N) := by
  let c₀ : circle := {c := 0, r := (dist 0 z)}
  let c₁ : circle := {c := 1, r := (dist 1 z)}
  have hc₀ : c₀ ∈ C (M_inf N) := by rw[c_in_C_M]; use 0; use 0; use z; constructor; simp_all only [dist_zero_left, Complex.norm_eq_abs, c₀]; constructor; apply M_M_inf' N 0 h₀; constructor; apply M_M_inf' N 0 h₀; exact hz
  have hc₁ : c₁ ∈ C (M_inf N) := by rw[c_in_C_M]; use 1; use 1; use z; constructor; simp_all only [dist_zero_left, Complex.norm_eq_abs, c₁]; constructor; apply M_M_inf' N 1 h₁; constructor; apply M_M_inf' N 1 h₁; exact hz
  have hcc : (starRingEnd ℂ) z ∈ c₀.points ∩ c₁.points := by rw [@Set.mem_inter_iff];  simp[circle.points]; rw[dist_comm, Complex.dist_eq, Complex.abs_eq_sqrt_sq_add_sq, Complex.abs_eq_sqrt_sq_add_sq, ←@Mathlib.Tactic.RingNF.add_neg, ←@Mathlib.Tactic.RingNF.add_neg, @Complex.add_re, @Complex.add_im]; simp
  apply icc_M_inf N; unfold icc; rw [@Set.mem_setOf]; use c₀; constructor; exact hc₀; use c₁
