import Construction.Chapter1.set_MInf

open Construction
/-
# Construction of negativ in M_inf

-/
lemma z_neg_M_inf (M: Set ℂ) (h₀: (0:ℂ)∈ M) (z : ℂ) (hz : z ∈ (M_inf M)) : -z ∈ (M_inf M) := by
  by_cases z0:(z=0)
  . simp [z0, M_M_inf M h₀]
  let l : line := {z₁ := 0, z₂ := z}
  let c : Construction.circle := {c := 0, r := (dist 0 z)}
  have hl : l ∈ L (M_inf M) := by
    refine ⟨0, z, ?_, M_M_inf M h₀, hz, ?_⟩
    simp only [l]
    simp  [eq_comm, z0]
  have hc : c ∈ C (M_inf M) := by
    refine ⟨0, 0, z, ?_, M_M_inf M h₀, M_M_inf M h₀, hz⟩
    simp [l, c]
  apply ilc_M_inf M
  refine ⟨c , hc, l, hl, ?_⟩
  simp [circle.points, line.points]
  refine ⟨2, (by push_cast; ring_nf)⟩
