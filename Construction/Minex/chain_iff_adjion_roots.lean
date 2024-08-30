import Construction.Chapter2.KZero
import Construction.NotMyCode.PR14987

section pre

variable {E : Type*} [Field E] {F : Type*} [Field F] [Algebra E F]

def succ_adjion (K: IntermediateField E F) (n : ℕ) (α: Fin n → Set F) := IntermediateField.adjoin K (⋃ i, α  i)
def SetOfRoots (K : IntermediateField E F) (M : Set F) := ∀ x : F, x ∈ M →   x * x ∈ K --∧ ¬(x ∈ K)
def succ_adjion_root  (K: IntermediateField E F) (n : ℕ) (α: Fin n → Set F) := ∀ i, SetOfRoots (IntermediateField.adjoin K (⋃ (j : Fin n), ⋃ (_ : j < i), α j)) (α i)

lemma succ_adjion_le (K: IntermediateField E F) (n m: ℕ) (αn: Fin n  → Set F) (αm: Fin m → Set F) : succ_adjion K n αn ≤ succ_adjion K (n+m) (Fin.append αn αm) := by sorry
lemma succ_adjion_root_split  (K: IntermediateField E F) (n : ℕ) (α: Fin n → Set F) (h : succ_adjion_root K n α) (α₁: Fin 1 → Set F) : SetOfRoots (IntermediateField.adjoin K (⋃  i, α i)) (α₁ 1) →  succ_adjion_root K (n+1) (Fin.append α α₁) := by sorry
lemma split_union_fin (n m: ℕ) (α₁ : Fin n → Set ℂ) (α₂ : Fin m → Set ℂ): ⋃ i, Fin.append α₁ α₂ i = (⋃ i, α₁ i) ∪ ⋃ i, α₂ i := by sorry
end pre


open IntermediateField

lemma chain_iff_adjion_roots (M : Set ℂ) (h₀ : 0 ∈ M) (h₁ : 1 ∈ M): (∃n, ∃ α: Fin n → Set ℂ, z ∈ (succ_adjion (K_zero M) n α) ∧ succ_adjion_root (K_zero M) n α) ↔  (∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (h: ∀i,  L i ≤ L (i + 1)),
    z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2)) := by sorry
