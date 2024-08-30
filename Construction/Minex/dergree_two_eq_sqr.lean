import Construction.Chapter2.KZero
import Construction.NotMyCode.PR14987

open IntermediateField Construction

section degree_two

variable {F: Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
variable (K : IntermediateField F E) (L : IntermediateField K E)


theorem dergree_two_eq_sqr :  FiniteDimensional.finrank K L = 2 ↔ ∃ x : E, x ^ 2 ∈ K ∧ ¬(x ∈ K) ∧ L = IntermediateField.adjoin K {x} := by

  sorry


end degree_two
