import Construction.Chapter2.MField
import Construction.NotMyCode.PR14987

--import Mathlib.RingTheory.Norm
import Mathlib.Deprecated.Subfield

open Construction IntermediateField



section gh
variable {E : Type*} [Field E] {F : Type*} [Field F] [Algebra E F] (K : IntermediateField E F)

noncomputable def K_zero (M : Set ℂ) : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ (M ∪ conj_set M)

def K_root : Set F := {x : F | x * x ∈ K}

def succ_adjion  (n : ℕ) (α: Fin n → Set F) := IntermediateField.adjoin K (⋃ i, α  i)

def SetOfRoots  (M : Set F) := ∀ x : F, x ∈ M →   x * x ∈ K --∧ ¬(x ∈ K)

def succ_adjion_root   (n : ℕ) (α: Fin n → Set F) := ∀ i, SetOfRoots (IntermediateField.adjoin K (⋃ (j : Fin n), ⋃ (_ : j ≤ i), α j)) (α i)

--lemma degree_two :  :=sorry

lemma succ_adjion_le (K: IntermediateField E F) (n m: ℕ) (αn: Fin n  → Set F) (αm: Fin m → Set F) : succ_adjion K n αn ≤ succ_adjion K (n+m) (Fin.append αn αm) := by
  unfold succ_adjion
  apply IntermediateField.adjoin.mono
  simp only [Set.iUnion_subset_iff]
  intro i
  rw [Set.subset_def]
  intro x
  simp only [Set.mem_iUnion]
  intro h
  use Fin.castAdd m i
  simp only [Fin.append_left, h]

end gh

open IntermediateField
lemma rat_mem_M_inf (M : Set ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M): ∀ x : ℚ, (algebraMap ℚ ℂ) x ∈ MField M h₀ h₁ := by
  intro x
  simp_all only [eq_ratCast]
  apply SubfieldClass.ratCast_mem


lemma adjoin_in_MField' (M : Set ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) (L : ℕ →  IntermediateField ℚ ℂ) (h: ∀i,  L i ≤ L (i + 1)) (hL₀: K_zero M = L 0) (n: ℕ) (h_deg: ∀ i < n, relfinrank (L i) (L (i+1)) = 2) : (L n).carrier ≤ MField M h₀ h₁ := by
  induction n
  case zero =>
    sorry
  case succ n Ih =>
    have hLn: (L n).carrier ≤ ↑(MField M h₀ h₁) := by
      apply Ih
      intro i hi
      specialize h_deg i (by linarith)
      exact h_deg
    have : ∃ N, L (n+1) = restrictScalars ℚ (adjoin (L n) N):=by
      sorry
    obtain ⟨N, hN⟩ := this
    have hN' : N ≤ (MField M h₀ h₁).toIntermediateField (rat_mem_M_inf M h₀ h₁) := by
      sorry
    have: L (n + 1) ≤ (MField M h₀ h₁).toIntermediateField (rat_mem_M_inf M h₀ h₁)  := by
      rw [hN]
      simp only [coe_toSubfield, restrictScalars_adjoin, adjoin_le_iff, Set.le_eq_subset,
        Set.union_subset_iff, SetLike.coe_subset_coe]
      exact ⟨hLn, hN'⟩
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring, coe_toSubalgebra,
      Set.le_eq_subset, Set.subset_def, SetLike.mem_coe]
    intro x hx
    simp_all only [SetLike.mem_coe]
    exact this hx


lemma test' (M : Set ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) (n : ℕ) : ∃ α: Fin n → Set ℂ, M_I M n ≤ (succ_adjion (K_zero M) n α) ∧ succ_adjion_root (K_zero M) n α ∧ ConjClosed (succ_adjion (K_zero M) n α) := by sorry



lemma chain_iff_adjion_roots (M : Set ℂ) (h₀ : 0 ∈ M) (h₁ : 1 ∈ M): (∃n, ∃ α: Fin n → Set ℂ, z ∈ (succ_adjion (K_zero M) n α) ∧ succ_adjion_root (K_zero M) n α) ↔  (∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (h: ∀i,  L i ≤ L (i + 1)),
    z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2)) := by
  refine ⟨?_, ?_⟩
  . intro h
    obtain ⟨n, α, hz, hr⟩ := h

    sorry
  intro h
  obtain ⟨n, L, mono, hz, hL₀, h_deg⟩ := h
  have (i: ℕ) (h : i < n):  ∃ x : ℂ,  restrictScalars ℚ (adjoin (L i) {x}) =  L (i+1) :=  by

    sorry
  --obtain ⟨x, hx⟩ := this i h
  let S (i : ℕ) (h: i < n) :=  {x : ℂ | restrictScalars ℚ (adjoin (L i) {x}) =  L (i+1)}
  have hS (i: ℕ) (h : i < n):  S i h ≠ ∅ := by
    rw [Mathlib.Tactic.PushNeg.ne_empty_eq_nonempty, Set.nonempty_def]
    apply this i h

  let α : Fin n → Set ℂ := λ i ↦ sorry-- S i (by linarith)

  refine ⟨n,?_, ?_, ?_⟩
  sorry
  sorry
  sorry


theorem Classfication_z_in_M_inf'  (M : Set ℂ) (z : ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) : z ∈ M_inf M ↔ ∃ (n : ℕ) (L : ℕ →  IntermediateField ℚ ℂ) (_: ∀i,  L i ≤ L (i + 1)),
    z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, relfinrank (L i) (L (i+1)) = 2) := by
  refine ⟨?_, ?_⟩
  . intro h
    rw [←chain_iff_adjion_roots M h₀ h₁]
    rw[ M_inf_in_M_I] at h
    obtain ⟨n, h ⟩ := h
    have: ∃ α,  M_I M n ≤ succ_adjion (K_zero M) n α ∧ succ_adjion_root (K_zero M) n α  ∧ ConjClosed (succ_adjion (K_zero M) n α) := by
      apply test' _ h₀ h₁
    obtain ⟨α, h', hr, _⟩ := this
    refine ⟨n, α,  h' h, hr⟩
  intro h
  obtain ⟨n, L, h, hz, hL₀, h_deg⟩ := h
  have hLn: (L n).carrier ≤ MField M h₀ h₁ := by
    apply adjoin_in_MField' M h₀ h₁ L h hL₀ n h_deg
  simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring, coe_toSubalgebra,
    Set.le_eq_subset, Set.subset_def, SetLike.mem_coe] at hLn
  simp_rw[ ←Subfield.mem_carrier] at hLn
  have : (MField M h₀ h₁).carrier = M_inf M := rfl
  rw[this] at hLn
  simp[hLn, hz]

open IntermediateField
lemma Classfication_z_in_M_inf_2m' (M : Set ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) (z : ℂ) :
  z ∈ M_inf M →  ∃ (m : ℕ) ,((2  : ℕ) ^ m) = Polynomial.natDegree (minpoly (K_zero M) z)  := by
  intro h
  rw[Classfication_z_in_M_inf' M z h₀ h₁] at h
  obtain ⟨n, L, h_sub, hLn, hK0, hi⟩ := h
  have: K_zero M ≤ L n := by
    rw [hK0]
    exact monotone_nat_of_le_succ h_sub (by linarith)
  have: Module (K_zero M) (IntermediateField.restrict this) := by sorry
  --have: FiniteDimensional.finrank (K_zero M) (L n) = 2^n := by sorry


  --rw[IntermediateField.adjoin.finrank]
  sorry


lemma Classfication_z_in_M_inf_2m (M : Set ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) (z : ℂ) :
  z ∈ M_inf M →  ∃ (m : ℕ) ,((2  : ℕ) ^ m) = Polynomial.degree (minpoly (K_zero M) z)  := by
  intro h
  rw[Classfication_z_in_M_inf' M z h₀ h₁] at h
  obtain ⟨n, L, h_sub, hLn, hK0, hi⟩ := h
  --have: Module (K_zero M) (L n) := by sorry
  --have: FiniteDimensional.finrank (K_zero M) (L n) = 2^n := by sorry


  --rw[IntermediateField.adjoin.finrank]
  sorry

-- section relfinrank_two

-- universe u v

-- variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

-- variable (A B : IntermediateField F E)

-- open IntermediateField Polynomial
-- lemma relfinrank_two_normal (h: A ≤ B) (h_dim: relfinrank  A B = 2) [Normal F A]: Normal F B := by
--   rw[relfinrank_eq_finrank_of_le h] at h_dim
--   --unfold FiniteDimensional.finrank Module.rank AddCommGroup.toAddCommMonoid instModuleSubtypeMem Algebra.toModule at h_dim
--   refine normal_iff.mpr ?_
--   intro x
--   refine ⟨?_, ?_⟩
--   .
--     sorry
--   .
--     sorry
