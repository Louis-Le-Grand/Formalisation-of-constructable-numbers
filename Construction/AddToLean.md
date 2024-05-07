# A list of things that should be added to Lean
While working with or in Lean, I have come across a number of things that I think should be added to Lean.

## Use for multipel Exists
There is an exist that handles multiple elements as a function, which makes using ``use`` complicated.

### Example

```lean
example (M : Set ℂ)(a₁ a₂ a₃ a₄ : M):
  let Z := {z | ∃ z₁ z₂ z₃ z₄: M, z ∈ intersection_line_line ↑z₁ ↑z₂ ↑z₃ ↑z₄}
  (intersection_line_line a₁ a₂ a₃ a₄) ⊆ Z := by sorry
```
Should be solvebel like 
```lean
example (M : Set ℂ)(a₁ a₂ a₃ a₄ : M):
  let Z := {z | ∃ z₁ z₂ z₃ z₄: M, z ∈ intersection_line_line ↑z₁ ↑z₂ ↑z₃ ↑z₄}
  (intersection_line_line a₁ a₂ a₃ a₄) ⊆ Z := by intro Z x hx; refine Set.mem_setOf.mpr ?_; use a₁ a₂ a₃ a₄; exact hx
````
But in stad you need split and simp multiple times.
```lean
example (M : Set ℂ)(a₁ a₂ a₃ a₄ : M):
  let Z := {z | ∃ z₁ z₂ z₃ z₄: M, z ∈ intersection_line_line ↑z₁ ↑z₂ ↑z₃ ↑z₄}
  (intersection_line_line a₁ a₂ a₃ a₄) ⊆ Z := by intro Z x hx; refine Set.mem_setOf.mpr ?_; refine SetCoe.exists.mpr ?_; simp; use a₁; constructor; simp; use a₂; constructor; simp; use a₃; constructor; simp; use a₄; constructor; simp; exact hx
```

## Element of a Union
There is a function for the union of two sets (``SetSet.subset_union_right``/``Set.subset_union_left``), but not for the union of a list of sets. This should be added.
```lean
example (a b c d : Set ℂ) : c ⊆ a ∪ b ∪ c ∪ d := by sorry
```
