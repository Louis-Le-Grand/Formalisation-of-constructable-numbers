import Construction.OLD.Geometry
import Construction.OLD.Set_of_construtable_numbers

--  M ⊆ ℂ mit 0,1 ∈ M
lemma add_inv_in_M_inf (M : Set ℂ) (hM : 0 ∈ M ∧ 1 ∈ M) : ∀ z : ℂ, z ∈ M_inf M → -z ∈ M_inf M := by
  intro z hz; by_cases h : z = 0; simp [h] at *; exact hz;
  let X := intersection_line_circle 0 0 z 0 z;  have hx: -z ∈ X := by sorry
  sorry

-- addition in M_inf
-- Complex conjugation
-- half of distance between z and w
-- half of angle between z and w
-- addition of angles
-- multiplication of positive real numbers
-- root of positive real number
-- polar coordinates of z
-- imaginary and real part of z
-- konstruktion von of I (imaginary unit)
