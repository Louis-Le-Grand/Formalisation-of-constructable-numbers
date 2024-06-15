import Construction.Chapter1.def


lemma M_in_ICL_M (M : Set ℂ) : M ⊆ ICL_M M := by
  unfold ICL_M
  intro x
  intro hx
  left
  left
  left
  exact hx

lemma M_I_Monotone (M : Set ℂ) : ∀n, M_I M n ⊆ M_I M (n+1) := by
  intro n
  apply M_in_ICL_M

lemma M_I_Monotone_elm (M : Set ℂ)(n : ℕ) : ∀ x, x ∈ M_I M n → x ∈ M_I M (Nat.succ n) := by
  intro n
  apply M_in_ICL_M

lemma M_I_Monotone' (M : Set ℂ)(n m : ℕ)(h: n ≤ m) :  M_I M n ⊆ M_I M m := by
  apply monotone_nat_of_le_succ
  apply M_I_Monotone
  exact h

lemma M_I_Monotone_elm' (M : Set ℂ)(n m : ℕ)(h: n ≤ m) : ∀ x, x ∈ M_I M n → x ∈ M_I M m := by
  intro x
  apply M_I_Monotone' M n m h

lemma M_in_M_I (M : Set ℂ) : ∀n, M ⊆ M_I M n := by
  intro n
  induction n
  simp [M_I]
  exact fun ⦃a⦄ a => a
  case succ n hn =>
    apply le_trans hn
    apply M_I_Monotone

lemma M_I_in_M_inf (M : Set ℂ)(m: ℕ): M_I M m ⊆ M_inf M := by
  unfold M_inf
  exact Set.subset_iUnion_of_subset m fun ⦃a⦄ a => a

lemma M_I_in_M_inf_elm (M : Set ℂ)(x : ℂ)(m: ℕ) :  x ∈ M_I M m → x ∈  M_inf M := by
  apply M_I_in_M_inf

lemma M_M_inf (M : Set ℂ) : M ⊆ M_inf M := by apply le_trans (M_in_M_I M 0) (M_I_in_M_inf M 0)

lemma M_inf_in_M_I (M : Set ℂ)(x:ℂ): x ∈ M_inf M ↔ ∃ n, x ∈ (M_I M n):= by
  apply Set.mem_iUnion

lemma M_inf_in_M_I' (M : Set ℂ)(x:ℂ): x ∈ M_inf M ↔ ∀ᶠ n in Filter.atTop, x ∈ M_I M n := by
  simp
  constructor
  . intro h
    have hn: ∃ n, x ∈ M_I M n := by
      exact (M_inf_in_M_I M x).mp h
    obtain ⟨n, hn⟩ := hn
    use n
    intro m hm
    apply M_I_Monotone_elm' M n m hm
    exact hn
  simp
  intro n hn
  apply M_I_in_M_inf_elm M x n
  apply hn
  simp

lemma L_M_inf_iff_M_M (M: Set ℂ): l ∈ L (M_inf M) ↔ ∀ᶠ n in Filter.atTop, l ∈ L (M_I M n) := by
  unfold L
  simp
  constructor
  intro h
  obtain ⟨z₁, z₂, h, hz₁, hz₂, Noteq⟩ := h
  rw[M_inf_in_M_I'] at hz₁ hz₂
  rw [←@Filter.eventually_atTop]
  filter_upwards [hz₁, hz₂]
  rw [h]
  simp
  intro a hz₁a hz₂a
  use z₁
  use z₂;
  intro h
  obtain ⟨n, hn⟩ := h
  have h: ∃ z₁ z₂, l = {z₁ := z₁, z₂ := z₂} ∧ z₁ ∈ M_I M n ∧ z₂ ∈ M_I M n ∧ z₁ ≠ z₂ := by
    apply hn
    simp
  obtain ⟨z₁, z₂, h, hz₁, hz₂, Noteq⟩ := h
  use z₁
  use z₂
  rw [h]
  simp
  constructor
  . exact M_I_in_M_inf_elm M z₁ n hz₁
  constructor
  . exact M_I_in_M_inf_elm M z₂ n hz₂
  exact Noteq

lemma C_M_inf_iff_M_M (M: Set ℂ): c ∈ C (M_inf M) ↔ ∀ᶠ n in Filter.atTop, c ∈ C (M_I M n) := by
  unfold C
  simp
  constructor
  intro h
  obtain ⟨z, r₁, r₂, h, hz, hr₁, hr₂⟩ := h
  rw[M_inf_in_M_I'] at hz hr₁ hr₂
  rw [←@Filter.eventually_atTop]
  filter_upwards [hz, hr₁, hr₂]
  rw [h]
  simp
  intro a hza hr₁a hr₂a
  use z
  use r₁
  use r₂
  intro h
  obtain ⟨n, hn⟩ := h
  have h: ∃ z r₁ r₂, c = {c:=z, r:=(dist r₁ r₂)} ∧ z ∈ M_I M n ∧ r₁ ∈ M_I M n ∧ r₂ ∈ M_I M n := by
    apply hn
    simp
  obtain ⟨z, r₁, r₂, h, hz, hr₁, hr₂⟩ := h
  use z
  use r₁
  use r₂
  rw [h]
  simp
  constructor
  . exact M_I_in_M_inf_elm M z n hz
  constructor
  . exact M_I_in_M_inf_elm M r₁ n hr₁
  exact M_I_in_M_inf_elm M r₂ n hr₂

lemma ill_M_inf (M: Set ℂ): ill (M_inf M) ⊆ M_inf M := by
  intro z
  intro hz
  unfold ill at hz
  rw [@Set.mem_setOf] at hz
  obtain ⟨l₁, hl₁, l₂, hl₂, hz⟩ := hz;
    rw [L_M_inf_iff_M_M] at hl₁ hl₂
  have zILL : ∃ n, z ∈ ill (M_I M n) := by
      unfold ill
      simp[exists_comm.mp]
      simp at hl₁ hl₂
      obtain ⟨a₁, hl₁⟩ := hl₁
      obtain ⟨a₂, hl₂⟩ := hl₂;let n := max a₁ a₂
      use n
      use l₁
      refine
      exists_and_left.mp ?h.a
      use l₂
      constructor
      . apply hl₁
        simp_all only [Set.mem_inter_iff, le_max_iff, le_refl, true_or, n]
      constructor
      . apply hl₂
        simp_all only [Set.mem_inter_iff, le_max_iff, le_refl, or_true, n]
      simp_all only [Set.mem_inter_iff, and_self]
  obtain ⟨n, hzn⟩ := zILL
  apply M_I_in_M_inf_elm M z n.succ
  unfold M_I ICL_M
  simp_all only [Filter.eventually_atTop, ge_iff_le, Set.mem_inter_iff, Set.mem_union,
    or_true, true_or]

lemma ilc_M_inf (M: Set ℂ): ilc (M_inf M) ⊆ M_inf M := by
  intro z
  intro hz
  unfold ilc at hz
  rw [@Set.mem_setOf] at hz
  obtain ⟨c, hc, l, hl, hz⟩ := hz;
    rw [C_M_inf_iff_M_M] at hc
  rw [L_M_inf_iff_M_M] at hl
  have zILC : ∃ n, z ∈ ilc (M_I M n) := by
    unfold ilc
    simp[exists_comm.mp]
    simp at hc hl
    obtain ⟨a₁, hc⟩ := hc
    obtain ⟨a₂, hl⟩ := hl;let n := max a₁ a₂
    use n
    use c
    refine exists_and_left.mp ?h.a
    use l
    constructor
    . apply hc
      simp_all only [Set.mem_inter_iff, le_max_iff, le_refl, true_or, n]
    constructor
    . apply hl
      simp_all only [Set.mem_inter_iff, le_max_iff, le_refl, or_true, n]
    simp_all only [Set.mem_inter_iff, and_self]
  obtain ⟨n, hzn⟩ := zILC
  apply M_I_in_M_inf_elm M z n.succ
  unfold M_I ICL_M
  simp_all only [Filter.eventually_atTop, ge_iff_le, Set.mem_inter_iff, Set.mem_union,
    or_true, true_or]

lemma icc_M_inf (M: Set ℂ): icc (M_inf M) ⊆ M_inf M := by
  intro z
  intro hz
  unfold icc at hz
  rw [@Set.mem_setOf] at hz
  obtain ⟨c₁, hc₁, c₂, hc₂, hz⟩ := hz;
  rw [C_M_inf_iff_M_M] at hc₁ hc₂
  have zICC : ∃ n, z ∈ icc (M_I M n) := by
    unfold icc
    simp[exists_comm.mp]
    simp at hc₁ hc₂
    obtain ⟨a₁, hc₁⟩ := hc₁
    obtain ⟨a₂, hc₂⟩ := hc₂
    let n := max a₁ a₂
    use n
    use c₁
    refine exists_and_left.mp ?h.a
    use c₂
    constructor
    . apply hc₁
      simp_all only [Set.mem_inter_iff, le_max_iff, le_refl, true_or, n]
    constructor
    . apply hc₂
      simp_all only [Set.mem_inter_iff, le_max_iff, le_refl, or_true, n]
    simp_all only [Set.mem_inter_iff, and_self]
  obtain ⟨n, hzn⟩ := zICC
  apply M_I_in_M_inf_elm M z n.succ
  unfold M_I ICL_M
  simp_all only [Filter.eventually_atTop, ge_iff_le, Set.mem_inter_iff, Set.mem_union,
    or_true, true_or]
