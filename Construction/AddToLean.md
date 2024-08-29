# Questions

## `aesop` 
Can I keep `aesop` or shloud I replaces it

## P-Q Formel 
Is there a way to use [Quadratic formula](https://en.wikipedia.org/wiki/Quadratic_formula)

I want to show that $\iota  \in L(\sqrt{(\frac{v ^ 2} {(4 * u ^ 2)} - \frac{w } {u})})$  and I have $u\cdot \iota ^ 2 + v\cdot \iota + w = 0$. My idea was 

Was to defiene the function and show that the roots are some element of L $\pm\sqrt{(\frac{v ^ 2} {(4 * u ^ 2)} - \frac{w } {u})}$.
```lean
have: u ≠ 0 := by sorry
have f_degree: degree f = 2 := by sorry
have f_ne_zero: f ≠ 0 := by sorry
have : ↑ι ∈ f.roots := by sorry
have : ↑(Multiset.card (f.roots)) ≤ 2 := by sorry
have : f.roots = { - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ),  - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ) } := by
  sorry --! Here I'm Stuck
have h: ι = - v/(2*u) + (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ) ∨ ι = - v/(2*u) - (v ^ 2 / (4 * u ^ 2) - w / u)^(1/2:ℂ) := by sorry
cases h <;> rename_i h <;> rw[h]
exact add_mem (div_mem (neg_mem (cast_L hv)) (mul_mem (ofNat_mem _ 2) (cast_L hu))) (IntermediateField.mem_adjoin_simple_self _ _)
exact sub_mem (div_mem (neg_mem (cast_L hv)) (mul_mem (ofNat_mem _ 2) (cast_L hu))) (IntermediateField.mem_adjoin_simple_self _ _)
```
## Stuctur of BA
What should i writte in the written part?
- Leaninfo?
- Missing in mathlib?

## Nest Wendsday meeting?
Can we have a meeting next wendsday?
- Date of talk
- final questions
- prove layout ...

<!-- 

## How to use $\mathbb{Q}$ as subset of $\mathbb{C}$?
```lean
 lemma Rat_ConjClosed : ConjClosed {x:ℂ|∃q:ℚ, ↑q = x} where
  equal := by simp only [conj_set, Set.mem_setOf_eq, exists_exists_eq_and, map_ratCast]
```

And for proving that $K_0$ is Conjugation closed, I want to use `conj_adjion`

## How to use `restrict_scalars`?
I have this lemma
```lean
lemma conj_adjion (K : IntermediateField ℚ ℂ) [ConjClosed K] (M : Set ℂ) [ConjClosed M] :
```
and want to use `restrict_scalars` to prove that
```lean 
lemma conj_adjion' (K : IntermediateField ℚ ℂ) (E : IntermediateField K ℂ) [ConjClosed E] (M : Set ℂ) [ConjClosed M] :
    ConjClosed (IntermediateField.adjoin E M) where
  equal := by
``` -->


# TODO
- Add $K_i$, $K_{\infty}$ and theorems about them (Not need for the construction proplems)
- Section about conjugtion closed sets and subfields (Not need for the construction proplems)


# A list of things that should be added to Lean
While working with or in Lean, I have come across a number of things that I think should be added to Lean.

## 
```lean
lemma K_le_K_adjion (K : IntermediateField F E) (M : Set E) ( x : E) (hx: x ∈ K) : x ∈ IntermediateField.adjoin K M := by
    unfold IntermediateField.adjoin
    apply Subfield.subset_closure
    apply Or.inl
    simp [hx]
```

## split union Fin
```lean
lemma split_union_fin (n m: ℕ) (α₁ : Fin n → Set ℂ) (α₂ : Fin m → Set ℂ): ⋃ i, Fin.append α₁ α₂ i = (⋃ i, α₁ i) ∪ ⋃ i, α₂ i := by
```

## apply lemma with multiple arguments
I hat a lemma whit multiple arguments, but I could not apply it with ``apply``. I had to use ``obtain`` and ``apply``. This should be possible with ``apply``. 
### Example
./Chapter1/basic_constructions.lean
```lean
lemma parallel_lines_M_inf ...
obtain ⟨q,_⟩ := (by apply l_in_L_M_imp (M_inf M) l₁; exact hl₁); exact q; obtain ⟨_,t⟩ := (by apply l_in_L_M_imp (M_inf M) l₁; exact hl₁); exact t;
[...]
```
## Complex.conj
```lean
example (z :ℂ): starRingEnd ℂ z = z.re - z.im *I := by
  refine ((fun {z w} ↦ ext_iff.mpr) ?_).symm; constructor; simp; simp
```
## Complex.inv
```lean
example (z:ℂ)(hz: z ≠ 0): z⁻¹ = z.re / (z.re^2+z.im^2)-(z.im/ (z.re^2+z.im^2) )*I:= by
   calc z⁻¹ = 1/ z := by simp
  _ = (starRingEnd ℂ z /  starRingEnd ℂ z)*(1/z) := by rw[div_self,one_mul]; simp_all only [ne_eq, map_eq_zero, not_false_eq_true]
  _ = (starRingEnd ℂ z /  (starRingEnd ℂ z * z)) := by rw [← @div_mul_eq_div_mul_one_div]
  _ = (starRingEnd ℂ z /  Complex.normSq z) := by rw[mul_comm, Complex.mul_conj z]
  _ = (starRingEnd ℂ z /  (z.re^2+z.im^2)) := by rw[Complex.normSq_apply]; norm_cast; rw[pow_two, pow_two]
  _ = ((z.re - z.im *I)/ (z.re^2+z.im^2) ) := by have h: starRingEnd ℂ z = z.re - z.im *I := by {refine ((fun {z w} ↦ ext_iff.mpr) ?_).symm; constructor; simp; simp}; rw[h]
  _ = z.re / (z.re^2+z.im^2)-(z.im/ (z.re^2+z.im^2) )*I := by rw [←div_sub_div_same, @mul_div_right_comm]
```

## Complex.root
$$ x^{\frac{1}{n}:\mathbb{C}}=\sqrt[n]{x} $$

## Root cast real to complex
For a real number $a \ge 0$, it should be posibbel to cast a real to complex root.
$$ \sqrt[\mathbb{R}]{a} = \sqrt[\mathbb{C}]{a}\quad \forall a \ge 0$$

## Complex root pow two
I cloud show it for real numbers greater than 0, but it should hold for all complex numbers and not be that complicated.
```lean
example (a:ℝ)(h: a ≥ 0): (a:ℂ) ^(1/2:ℂ) * (↑a)^(1/2:ℂ) = a := by
  rw [← pow_two, ←root_cast]
  norm_cast
  rw[←Real.rpow_natCast]
  push_cast
  . rw[←Real.rpow_mul, one_div_mul_eq_div, div_self, Real.rpow_one]
    . simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    . exact h
  . exact h
```

## Complex root real imaginary
For a complex number $z = a + bI$, the root of $z$ is equivalent to 
$$
\sqrt{z} = \sqrt{a + bI,}   = \sqrt{ \frac{a + \sqrt{a^2 + b^2}}{2} } + I\frac{b}{|b|}\sqrt{\frac{\sqrt{a^2 + b^2} - a}{2} } 
$$

```lean
lemma root_copmlex (z : ℂ): z ^ (1/2:ℂ) = (((abs z)+z.re)/2)^ (1/2:ℂ)+I*z.im/|z.im| *
    (((abs z )-z.re)/2)^ (1/2:ℂ) := by sorry
```


## Element of a Union
There is a function for the union of two sets (``SetSet.subset_union_right``/``Set.subset_union_left``), but not for the union of a list of sets. This should be added.
```lean
example (a b c d : Set ℂ) : c ⊆ a ∪ b ∪ c ∪ d := by sorry
```

## lemmas for Complex.abs
in lemma int_cir_cir_4'

```lean
example (a b : ℂ) (h: a ≠ b): Complex.abs (a-b / Complex.abs (a-b)) = 1 := by
```

```lean
example (a b  : ℂ) (h: a ≠ b): Complex.abs ((a - b ) / Complex.abs (a - b)) = 1 := by
  calc
    _ = Complex.abs (a - b)/ Complex.abs (Complex.abs (a - b))  := by exact map_div₀ Complex.abs (a-b) (Complex.abs (a-b))
    _ = 1 := by simp; rw[div_self]; rw[←Complex.dist_eq, dist_ne_zero]; exact h

example (a b  : ℂ): Complex.abs (a*b) = Complex.abs a * Complex.abs b := by
  rw [@AbsoluteValue.map_mul]
```