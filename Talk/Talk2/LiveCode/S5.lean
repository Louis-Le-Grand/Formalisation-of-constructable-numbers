import Construction.Chapter1.set_MInf

/-
# Construction of Addition in M_inf
The proof is stuctur as follows:
  - define two circles `c₁` and `c₂` with centers `z₁` and `z₂` and radii `dist 0 z₂` and `dist 0 z₁`.
  - Show that `c₁` and `c₂` are in `C (M_inf M)`.
  - Apply the `icc_M_inf` lemma to show that `z₁ + z₂` is in `icc_M_inf`.
-/
open Construction
lemma add_M_Inf (M: Set ℂ) (h₀: (0:ℂ)∈ M) (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ (M_inf M)) (hz₂ : z₂ ∈ (M_inf M)):
     z₁ + z₂ ∈ (M_inf M) := by
  let c₁ : Construction.circle := {c := z₁, r := (dist 0 z₂)}
  let c₂ : Construction.circle := {c := z₂, r := (dist 0 z₁)}
  have hc₁ : c₁ ∈ C (M_inf M) := by
    use z₁, 0, z₂
    refine ⟨?_, (by exact hz₁), (by exact M_M_inf M h₀), (by exact hz₂)⟩
    simp [c₁]
  have hc₂ : c₂ ∈ C (M_inf M) := by
    use z₂, 0, z₁
    refine ⟨?_, (by exact hz₂), (by exact M_M_inf M h₀), (by exact hz₁)⟩
    simp [c₂]
  apply icc_M_inf M
  refine ⟨c₁, (by exact hc₁), c₂, (by exact hc₂), ?_⟩
  simp [circle.points, Set.mem_inter_iff]
