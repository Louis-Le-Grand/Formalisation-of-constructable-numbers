# A list of things that should be added to Lean
While working with or in Lean, I have come across a number of things that I think should be added to Lean.

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