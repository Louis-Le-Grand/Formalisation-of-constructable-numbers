import Construction.NotMyCode.DegreeTwo
import Construction.NotMyCode.PR14987
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Rat

open IntermediateField

namespace QuadraticChain

abbrev Field := IntermediateField ℚ ℂ

lemma adjoin_union (s t : Set ℂ) :
    adjoin ℚ (s ∪ t) = adjoin ℚ s ⊔ adjoin ℚ t := by
  apply le_antisymm
  · exact adjoin_le_iff.mpr (Set.union_subset
      (fun x hx => (le_sup_left : adjoin ℚ s ≤ adjoin ℚ s ⊔ adjoin ℚ t)
        (subset_adjoin ℚ s hx))
      (fun x hx => (le_sup_right : adjoin ℚ t ≤ adjoin ℚ s ⊔ adjoin ℚ t)
        (subset_adjoin ℚ t hx)))
  · exact sup_le (adjoin.mono _ _ _ Set.subset_union_left)
      (adjoin.mono _ _ _ Set.subset_union_right)

lemma restrict_adjoin (K : Field) (s : Set ℂ) :
    (adjoin K s).restrictScalars ℚ = K ⊔ adjoin ℚ s := by
  rw [restrictScalars_adjoin, adjoin_union, adjoin_self]

/-- A finite tower of square-root adjunctions, allowing redundant steps. -/
inductive Tower (K : Field) : Field → Prop
  | base : Tower K K
  | step {L : Field} : Tower K L → (x : ℂ) → x ^ 2 ∈ L →
      Tower K (L ⊔ adjoin ℚ {x})

namespace Tower

lemma le {K L : Field} (h : Tower K L) : K ≤ L := by
  induction h with
  | base => exact le_rfl
  | step _ x _ ih => exact ih.trans le_sup_left

lemma trans {K L P : Field} (h : Tower K L) (g : Tower L P) : Tower K P := by
  induction g with
  | base => exact h
  | step _ x hx ih => exact ih.step x hx

lemma baseChange {K L : Field} (h : Tower K L) (P : Field) (hKP : K ≤ P) :
    Tower P (P ⊔ L) := by
  induction h with
  | base => simpa only [sup_eq_left.mpr hKP] using (Tower.base : Tower P P)
  | @step L _ x hx ih =>
      simpa only [sup_assoc] using ih.step x ((le_sup_right : L ≤ P ⊔ L) hx)

lemma sup {K L P : Field} (h : Tower K L) (g : Tower K P) : Tower K (L ⊔ P) :=
  h.trans (g.baseChange L h.le)

end Tower

/-- The intermediate field of elements lying in finite square-root towers over `K`. -/
noncomputable def closure (K : Field) : Field where
  carrier := {x | ∃ L, Tower K L ∧ x ∈ L}
  zero_mem' := ⟨K, .base, K.zero_mem⟩
  one_mem' := ⟨K, .base, K.one_mem⟩
  add_mem' := by
    rintro x y ⟨L, hL, hx⟩ ⟨P, hP, hy⟩
    exact ⟨L ⊔ P, hL.sup hP, (L ⊔ P).add_mem
      ((le_sup_left : L ≤ L ⊔ P) hx) ((le_sup_right : P ≤ L ⊔ P) hy)⟩
  mul_mem' := by
    rintro x y ⟨L, hL, hx⟩ ⟨P, hP, hy⟩
    exact ⟨L ⊔ P, hL.sup hP, (L ⊔ P).mul_mem
      ((le_sup_left : L ≤ L ⊔ P) hx) ((le_sup_right : P ≤ L ⊔ P) hy)⟩
  inv_mem' := by
    rintro x ⟨L, hL, hx⟩
    exact ⟨L, hL, inv_mem hx⟩
  algebraMap_mem' := fun a => ⟨K, .base, K.algebraMap_mem a⟩

lemma le_closure (K : Field) : K ≤ closure K := fun _ hx => ⟨K, .base, hx⟩

lemma root_mem_closure (K : Field) {x : ℂ} (hx : x ^ 2 ∈ closure K) : x ∈ closure K := by
  obtain ⟨L, hL, hx⟩ := hx
  exact ⟨L ⊔ adjoin ℚ {x}, hL.step x hx,
    (le_sup_right : adjoin ℚ {x} ≤ L ⊔ adjoin ℚ {x}) (mem_adjoin_simple_self ℚ x)⟩

/-- Remove redundant adjunctions to obtain a chain with every step of degree two. -/
lemma Tower.exists_chain {K P : Field} (h : Tower K P) :
    ∃ (n : ℕ) (L : ℕ → Field), (∀ i, L i ≤ L (i + 1)) ∧
      L 0 = K ∧ L n = P ∧ ∀ i < n, relfinrank (L i) (L (i + 1)) = 2 := by
  induction h with
  | base => exact ⟨0, fun _ => K, fun _ => le_rfl, rfl, rfl, by omega⟩
  | @step P _ x hx ih =>
    by_cases hxP : x ∈ P
    · have he : P ⊔ adjoin ℚ {x} = P :=
        sup_eq_left.mpr (adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxP))
      simpa only [he] using ih
    · obtain ⟨n, L, hmono, hzero, hn, hdeg⟩ := ih
      let Q := P ⊔ adjoin ℚ {x}
      have hPQ : P ≤ Q := le_sup_left
      have hdegree : relfinrank P Q = 2 := by
        rw [relfinrank_eq_finrank_of_le hPQ, dergree_two_eq_sqr]
        refine ⟨x, hx, hxP, ?_⟩
        apply restrictScalars_injective ℚ
        rw [extendScalars_restrictScalars, restrict_adjoin]
      let L' : ℕ → Field := fun i => if i ≤ n then L i else Q
      refine ⟨n + 1, L', ?_, ?_, ?_, ?_⟩
      · intro i
        dsimp [L']
        split_ifs with hi hj
        · exact hmono i
        · have : i = n := by omega
          subst i
          simpa only [hn] using hPQ
        · omega
        · exact le_rfl
      · simpa [L'] using hzero
      · simp [L']
      · intro i hi
        by_cases hin : i < n
        · simpa [L', show i ≤ n by omega, show i + 1 ≤ n by omega] using hdeg i hin
        · have : i = n := by omega
          subst i
          simpa [L', hn] using hdegree

lemma tower_of_chain (K : Field) (n : ℕ) (L : ℕ → Field)
    (hmono : ∀ i, L i ≤ L (i + 1)) (hzero : K = L 0)
    (hdeg : ∀ i < n, relfinrank (L i) (L (i + 1)) = 2) : Tower K (L n) := by
  induction n with
  | zero => simpa only [← hzero] using (Tower.base : Tower K K)
  | succ n ih =>
    have hprev := ih (fun i hi => hdeg i (by omega))
    have hd := hdeg n (by omega)
    rw [relfinrank_eq_finrank_of_le (hmono n), dergree_two_eq_sqr] at hd
    obtain ⟨x, hx, _, he⟩ := hd
    have he' : L (n + 1) = L n ⊔ adjoin ℚ {x} := by
      have hh := congrArg (IntermediateField.restrictScalars ℚ) he
      simpa only [extendScalars_restrictScalars, restrict_adjoin] using hh
    rw [he']
    exact hprev.step x hx

end QuadraticChain
