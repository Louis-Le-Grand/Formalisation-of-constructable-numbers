import Construction.Chapter2.ClasificationMinf

namespace QuadraticChain
open IntermediateField Construction

lemma Tower.exists_layers {K P : QuadraticChain.Field} (h : Tower K P) :
    ∃ (n : ℕ) (α : Fin n → Set ℂ),
      P = (succ_adjion K n α).restrictScalars ℚ ∧ succ_adjion_root K n α := by
  induction h with
  | base =>
    refine ⟨0, Fin.elim0, ?_, ?_⟩
    · simp [succ_adjion]
    · intro i
      exact Fin.elim0 i
  | @step P _ x hx ih =>
    obtain ⟨n, α, he, hr⟩ := ih
    let β : Fin 1 → Set ℂ := fun _ => {x}
    have hb : (⋃ i, β i) = {x} := by simp [β]
    refine ⟨n + 1, Fin.append α β, ?_, ?_⟩
    · rw [he]
      simp only [succ_adjion, split_union_fin, hb, restrict_adjoin,
        QuadraticChain.adjoin_union, sup_assoc]
    · apply succ_adjion_root_split K n α hr β
      intro a ha
      have ha' : a = x := Set.mem_singleton_iff.mp ha
      subst a
      have hx' : x ^ 2 ∈ succ_adjion K n α := by
        rw [he] at hx
        exact hx
      simpa only [sq] using hx'

lemma layers_le_closure (K : QuadraticChain.Field) (n : ℕ) (α : Fin n → Set ℂ)
    (hr : succ_adjion_root K n α) :
    (succ_adjion K n α).restrictScalars ℚ ≤ QuadraticChain.closure K := by
  have hα : ∀ i, α i ⊆ QuadraticChain.closure K := by
    intro i
    induction i using WellFoundedLT.induction
    rename_i j ih
    intro x hx
    apply root_mem_closure
    have hp : (adjoin K (⋃ k : Fin n, ⋃ (_ : k < j), α k)).restrictScalars ℚ ≤
        QuadraticChain.closure K := by
      rw [restrict_adjoin]
      refine sup_le (le_closure K) (adjoin_le_iff.mpr ?_)
      intro y hy
      obtain ⟨k, hy⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hk, hy⟩ := Set.mem_iUnion.mp hy
      exact ih k hk hy
    exact hp (by simpa only [sq] using hr j x hx)
  rw [succ_adjion, restrict_adjoin]
  exact sup_le (le_closure K) (adjoin_le_iff.mpr (Set.iUnion_subset hα))

end QuadraticChain
