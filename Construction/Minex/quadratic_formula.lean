import Mathlib

open Polynomial

example (ι u v w : ℂ) (h:  u * ι ^ 2 +  v * ι + w = 0) (hu: u≠0): ι = - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ) ∨ ι = - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ):= by
    let f : (Polynomial ℂ) :=  C u * X ^ 2 + C v * X + C w
    have f_degree: degree f = 2 := by
      simp[f]
      compute_degree!
    have f_ne_zero: f ≠ 0 := by
      rw [← @zero_le_degree_iff, f_degree]
      norm_num
    have : ↑ι ∈ f.roots := by
      rw [mem_roots']
      refine ⟨f_ne_zero, ?_⟩
      simp[f]
      rw[← h]
    have card_root: ↑(Multiset.card (f.roots)) ≤ 2 := by
      exact le_trans (b:= f.natDegree) (Polynomial.card_roots' f) (natDegree_quadratic_le)
    have: f.roots = { - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ),  - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ) } := by
      have: ↑(Multiset.card { - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ),  - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ) })= 2 := by
        simp only [one_div, Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton, Nat.reduceAdd]
      -- have: { - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ),  - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ) } =  (- v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ)) ::ₘ { - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ)} := by
      --   simp only [one_div, Multiset.insert_eq_cons]
      have: { - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ),  - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ) } ≤ f.roots := by
        rw [Multiset.card_eq_two] at this
        obtain ⟨x, y, hxy⟩ := this
        rw [hxy]
        simp only [Multiset.insert_eq_cons]
        rw[←Multiset.singleton_add]
        sorry
      symm
      apply Multiset.eq_of_le_of_card_le this card_root
    rename_i h
    rw[this] at h
    simp_all only [one_div, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]

example (ι u v w : ℝ) (h:  u * ι ^ 2 +  v * ι + w = 0) (hu: u≠0): ι = - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℝ) ∨ ι = - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℝ):= by
    let f : (Polynomial ℝ) :=  C u * X ^ 2 + C v * X + C w
    have f_degree: degree f = 2 := by
      simp[f]
      compute_degree!
    have f_ne_zero: f ≠ 0 := by
      rw [← @zero_le_degree_iff, f_degree]
      norm_num
    have : ↑ι ∈ f.roots := by
      rw [mem_roots']
      refine ⟨f_ne_zero, ?_⟩
      simp[f]
      rw[← h]
    have card_root: ↑(Multiset.card (f.roots)) ≤ 2 := by
      exact le_trans (b:= f.natDegree) (Polynomial.card_roots' f) (natDegree_quadratic_le)
    have: f.roots = { - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℝ),  - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℝ) } := by
      -- have: ↑(Multiset.card { - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℝ),  - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℝ) })= 2 := by
      --   simp only [one_div, Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton, Nat.reduceAdd]
      -- rw [Multiset.card_eq_two] at this
      -- obtain ⟨x, y, hxy⟩ := this
      -- rw [hxy]
      symm
      simp only [Multiset.insert_eq_cons]
      rw[←Multiset.singleton_add, Multiset.add_singleton_eq_iff]
      refine ⟨?_,?_⟩
      . simp only [one_div, mem_roots', ne_eq]
        refine ⟨f_ne_zero, ?_⟩
        simp only [IsRoot.def, eval_add, eval_mul, eval_C, eval_pow, eval_X, f]
        simp_rw[sub_sq, div_pow, mul_pow]
        have: 0 ≤ v ^ 2 / (4 * u ^ 2) - w / u := by sorry
        calc _ = (1/4) * v^2 * (u / u) * 1/ u  + v * (2/ 2:ℝ) * (u/u) * (v ^ 2 / (4 * u ^ 2) - w / u) ^ (2⁻¹:ℝ) + u * ((v ^ 2 / (4 * u ^ 2) - w / u) ^ (2⁻¹:ℝ)) ^ 2 - v^2 / (2 * u) - v*(v ^ 2 / (4 * u ^ 2) - w / u) ^ (2⁻¹:ℝ) + w := by ring_nf
          _ = (1/4) * v^2 * 1/ u  + v * (v ^ 2 / (4 * u ^ 2) - w / u) ^ (2⁻¹:ℝ) + u * ((v ^ 2 / (4 * u ^ 2) - w / u) ^ (1 / 2:ℝ)) ^ 2 - v^2 / (2 * u) - v*(v ^ 2 / (4 * u ^ 2) - w / u) ^ (2⁻¹:ℝ) + w := by simp only [one_div, div_self hu, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
          _ = (1/4) * v^2 * 1/ u  + v * (v ^ 2 / (4 * u ^ 2) - w / u) ^ (2⁻¹:ℝ) +  (v ^ 2) * 1 / 4  * (u / u) * 1/u - w * (u / u) - v^2 / (2 * u) - v*(v ^ 2 / (4 * u ^ 2) - w / u) ^ (2⁻¹:ℝ) + w := by rw[←Real.sqrt_eq_rpow (v ^ 2 / (4 * u ^ 2) - w / u), Real.sq_sqrt this]; ring_nf
          _ = 0 := by simp only [one_div, mul_one, ne_eq, hu, not_false_eq_true, div_self]; ring_nf



      sorry
    rename_i h
    rw[this] at h
    simp_all only [one_div, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]

example (a : ℝ) (h: 0 ≤ a) : (a ^ (1/2:ℝ))^2 = a := by
  symm
  refine (Real.sqrt_eq_iff_eq_sq h ?hy).mp ?_
  . rw[←Real.sqrt_eq_rpow a]; exact Real.sqrt_nonneg a
  exact Real.sqrt_eq_rpow a
