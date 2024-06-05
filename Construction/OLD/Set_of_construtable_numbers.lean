import Construction.OLD.Geometry

-- Definition of construction of M_inf
def Z_M (M : Set ℂ) : Set ℂ :=
  M ∪ {z : ℂ | ∃ c₁ r₁ r₂ c₂ r₃ r₄ : M, z ∈ intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄} ∪
  {z : ℂ | ∃ c r₁ r₂ z₁ z₂ : M, z ∈ intersection_line_circle c r₁ r₂ z₁ z₂} ∪
  {z : ℂ | ∃ z₁ z₂ z₃ z₄ : M, z ∈ intersection_line_line z₁ z₂ z₃ z₄}

def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => Z_M (M_I M n)

def M_inf (M : Set ℂ) : Set ℂ :=  ⋃ (n : ℕ), M_I M n


@[simp] lemma M_0 (M : Set ℂ) : M_I M 0 = M := rfl

lemma Z_M_eq (M : Set ℂ) : Z_M M = (M ∪
    {z | ∃ c₁ r₁ r₂ c₂ r₃ r₄ : M, z ∈ intersection_circle_circle ↑c₁ ↑r₁ ↑r₂ ↑c₂ ↑r₃ ↑r₄} ∪
    {z | ∃ c r₁ r₂ z₁ z₂: M, z ∈ intersection_line_circle ↑c ↑r₁ ↑r₂ ↑z₁ ↑z₂} ∪
    {z | ∃ z₁ z₂ z₃ z₄: M, z ∈ intersection_line_line ↑z₁ ↑z₂ ↑z₃ ↑z₄}) := by unfold Z_M; simp

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

lemma M_inf_in_M_I (M : Set ℂ) : ∀ x ∈ M_inf M, ∃ n, x ∈ (M_I M n):= by
  intro x; apply Set.mem_iUnion.mp

lemma M_inf_in_M_I' (M : Set ℂ)(x:ℂ): x ∈ M_inf M ↔ ∀ᶠ n in Filter.atTop, x ∈ M_I M n := by
  simp; constructor; intro h; have hn: ∃ n, x ∈ M_I M n := by apply M_inf_in_M_I; exact h;
  obtain ⟨n, hn⟩ := hn; use n; intro m hm; apply M_I_Monotone_elm' M n m hm; exact hn
  simp; intro n hn; apply M_I_in_M_inf' M x n; apply hn; simp



--Todo Delet or do as exercise for filters

lemma Int_cc_in_M_inf' (M : Set ℂ)(c₁ r₁ r₂ c₂ r₃ r₄ : M_inf M): intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ ⊆ M_inf M := by
  have h₁: ∀ᶠ n in Filter.atTop, ↑c₁ ∈ M_I M n:= by rw[←M_inf_in_M_I']; exact Subtype.coe_prop c₁
  have h₂: ∀ᶠ n in Filter.atTop, ↑r₁ ∈ M_I M n:= by rw[←M_inf_in_M_I']; exact Subtype.coe_prop r₁
  have h₃: ∀ᶠ n in Filter.atTop, ↑r₂ ∈ M_I M n:= by rw[←M_inf_in_M_I']; exact Subtype.coe_prop r₂
  have h₄: ∀ᶠ n in Filter.atTop, ↑c₂ ∈ M_I M n:= by rw[←M_inf_in_M_I']; exact Subtype.coe_prop c₂
  have h₅: ∀ᶠ n in Filter.atTop, ↑r₃ ∈ M_I M n:= by rw[←M_inf_in_M_I']; exact Subtype.coe_prop r₃
  have h₆: ∀ᶠ n in Filter.atTop, ↑r₄ ∈ M_I M n:= by rw[←M_inf_in_M_I']; exact Subtype.coe_prop r₄
  have h: ∀ᶠ n in Filter.atTop,↑c₁ ∈ M_I M n ∧ ↑r₁ ∈ M_I M n ∧ ↑r₂ ∈ M_I M n ∧ ↑c₂ ∈ M_I M n ∧ ↑r₃ ∈ M_I M n ∧ ↑r₄ ∈ M_I M n := by sorry
  have h' (x : intersection_circle_circle ↑c₁ ↑r₁ ↑r₂ ↑c₂ ↑r₃ ↑r₄): ∀ᶠ n in Filter.atTop, ↑x ∈  M_I M n := by sorry
  rw [@Set.subset_def]; intro x hx
  -- eventually.and to show that the conciontion holds for some n
  -- eventually.exist
  --use M_inf_in_M_I iff
  sorry

lemma Int_cc_in_M_inf'' (M : Set ℂ)(c₁ r₁ r₂ c₂ r₃ r₄ : M_inf M): intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ ⊆ M_inf M := by
  have h₁: ∃ n, ↑c₁ ∈ M_I M n:= by apply M_inf_in_M_I; exact Subtype.coe_prop c₁
  have h₂: ∃ n, ↑r₁ ∈ M_I M n:= by apply M_inf_in_M_I; exact Subtype.coe_prop r₁
  have h₃: ∃ n, ↑r₂ ∈ M_I M n:= by apply M_inf_in_M_I; exact Subtype.coe_prop r₂
  have h₄: ∃ n, ↑c₂ ∈ M_I M n:= by apply M_inf_in_M_I; exact Subtype.coe_prop c₂
  have h₅: ∃ n, ↑r₃ ∈ M_I M n:= by apply M_inf_in_M_I; exact Subtype.coe_prop r₃
  have h₆: ∃ n, ↑r₄ ∈ M_I M n:= by apply M_inf_in_M_I; exact Subtype.coe_prop r₄
  rw [@Set.subset_def]; intro x hx; apply M_I_in_M_inf;
  sorry; sorry




lemma M_in_M_inf (M : Set ℂ) : Z_M (M_inf M) = M_inf M := by
  rw [@Set.ext_iff]; intro x; constructor; case  mpr => apply M_in_Z_M;
  intro hx; unfold Z_M at hx; --simp only [@Set.mem_union, @or_assoc] at hx;
  sorry

lemma int_ll_in_M_inf (M : Set ℂ): ∀ z₁ z₂ z₃ z₄:M_inf M, intersection_line_line z₁ z₂ z₃ z₄ ⊆ M_inf M := by
  have h: Z_M (M_inf M) ⊆  M_inf M := by {refine Eq.subset (M_in_M_inf M)}; intro a₁ a₂ a₃ a₄;
  let Z := {z | ∃ z₁ z₂ z₃ z₄: M_inf M, z ∈ intersection_line_line ↑z₁ ↑z₂ ↑z₃ ↑z₄}
  have h': Z ⊆ M_inf M := by apply subset_trans (b:= Z_M (M_inf M)); apply Set.subset_union_right; exact h
  have h'': intersection_line_line a₁ a₂ a₃ a₄ ⊆ Z := by intro x hx; refine Set.mem_setOf.mpr ?_; refine SetCoe.exists.mpr ?_; simp; use a₁; constructor; simp; use a₂; constructor; simp; use a₃; constructor; simp; use a₄; constructor; simp; exact hx
  apply subset_trans (b:=Z); exact h''; exact h'

lemma int_lc_in_M_inf (M : Set ℂ): ∀ c r₁ r₂ z₁ z₂:M_inf M, intersection_line_circle c r₁ r₂ z₁ z₂ ⊆ M_inf M := by
  have h: Z_M (M_inf M) ⊆  M_inf M := by {refine Eq.subset (M_in_M_inf M)}; intro a₁ a₂ a₃ a₄ a₅;
  let Z := {z | ∃ c r₁ r₂ z₁ z₂: M_inf M, z ∈ intersection_line_circle ↑c ↑r₁ ↑r₂ ↑z₁ ↑z₂}
  have h': Z ⊆ M_inf M := by apply subset_trans (b:= Z_M (M_inf M)); unfold Z_M; rw [@Set.union_assoc]; apply subset_trans (b:= ({z | ∃ c r₁ r₂ z₁ z₂: M_inf M, z ∈ intersection_line_circle ↑c ↑r₁ ↑r₂ ↑z₁ ↑z₂} ∪
      {z | ∃ z₁ z₂ z₃ z₄ :M_inf M, z ∈ intersection_line_line ↑z₁ ↑z₂ ↑z₃ ↑z₄})); apply Set.subset_union_left; apply Set.subset_union_right; exact h
  have h'': intersection_line_circle a₁ a₂ a₃ a₄ a₅ ⊆ Z := by intro x hx; refine Set.mem_setOf.mpr ?_; refine SetCoe.exists.mpr ?_; simp; use a₁, by simp, a₂, by simp, a₃, by simp, a₄, by simp, a₅, by simp
  apply subset_trans (b:=Z); exact h''; exact h'

lemma int_cc_in_M_inf (M : Set ℂ): ∀ c₁ r₁ r₂ c₂ r₃ r₄:M_inf M, intersection_circle_circle c₁ r₁ r₂ c₂ r₃ r₄ ⊆ M_inf M := by
  have h: Z_M (M_inf M) ⊆  M_inf M := by {refine Eq.subset (M_in_M_inf M)}; intro a₁ a₂ a₃ a₄ a₅ a₆;
  let Z := {z | ∃ c₁ r₁ r₂ c₂ r₃ r₄: M_inf M, z ∈ intersection_circle_circle ↑c₁ ↑r₁ ↑r₂ ↑c₂ ↑r₃ ↑r₄}
  have h': Z ⊆ M_inf M := by apply subset_trans (b:= Z_M (M_inf M)); unfold Z_M; rw [@Set.union_assoc]; apply subset_trans (b:= M_inf M ∪ {z | ∃ c₁ r₁ r₂ c₂ r₃ r₄: M_inf M, z ∈ intersection_circle_circle ↑c₁ ↑r₁ ↑r₂ ↑c₂ ↑r₃ ↑r₄}); apply Set.subset_union_right; apply Set.subset_union_left; exact h
  have h'': intersection_circle_circle a₁ a₂ a₃ a₄ a₅ a₆ ⊆ Z := by intro x hx; refine Set.mem_setOf.mpr ?_; refine SetCoe.exists.mpr ?_; simp; use a₁; constructor; simp; use a₂; constructor; simp; use a₃; constructor; simp; use a₄; constructor; simp; use a₅; constructor; simp; use a₆; constructor; simp; exact hx
  apply subset_trans (b:=Z); exact h''; exact h'
