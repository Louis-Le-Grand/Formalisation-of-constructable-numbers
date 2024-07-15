import Construction.Chapter1.set_MInf

/-
# Construction of Addition in M_inf
The proof is stuctur as follows:
  - define two circles `c₁` and `c₂` with centers `z₁` and `z₂` and radii `dist 0 z₂` and `dist 0 z₁`
  - and a line `l` with points `z₁` and `0`, therefor case `z₁ = 0` is handled separately
  - Show that `c₁` and `c₂` are in `C (M_inf M)` and `l` is in `L (M_inf M)`
  - case `z₁ = z₂` apply `ilc_M_inf` lemma to show that `z₁ + z₂` is in `ilc_M_inf`
  - case `z₁ ≠ z₂` apply the `icc_M_inf` lemma to show that `z₁ + z₂` is in `icc_M_inf`.
-/
open Construction
lemma add_M_Inf (M: Set ℂ) (h₀: (0:ℂ)∈ M) (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ (M_inf M)) (hz₂ : z₂ ∈ (M_inf M)):
     z₁ + z₂ ∈ (M_inf M) := by
  by_cases hz₁0: (z₁ = 0)
  . simp only [hz₁0, zero_add, hz₂]
  let c₁ : Construction.circle := {c := z₁, r := (dist 0 z₂)}
  let c₂ : Construction.circle := {c := z₂, r := (dist 0 z₁)}
  let l: line := {z₁ := z₁, z₂ := 0}
  have hc₁ : c₁ ∈ C (M_inf M) := by
    refine ⟨z₁, 0, z₂, ?_, hz₁,M_M_inf M h₀, hz₂⟩
    simp [c₁]
  have hc₂ : c₂ ∈ C (M_inf M) := by
    refine ⟨z₂, 0, z₁, ?_,hz₂,M_M_inf M h₀,hz₁⟩
    simp [c₂]
  have hl : l ∈ L (M_inf M) := by
    refine ⟨z₁, 0, ?_, hz₁, M_M_inf M h₀, hz₁0⟩
    simp [l, hz₁0]
  by_cases h: (z₁ = z₂)
  . refine ilc_M_inf M ⟨c₁, hc₁, l, hl, ⟨?_, ⟨2,?_⟩⟩⟩
    . simp [circle.points, h]
    . simp [h, two_mul]
  . refine icc_M_inf M ⟨c₁,hc₁, c₂,hc₂, ?_⟩
    simp [circle.points, Set.mem_inter_iff]
    exact circle_not_eq_iff  (by exact h)
