module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace JSP233.StarMidpoint158375

theorem half_square_step (n : ℕ) :
    (1 : ℝ)/((n : ℝ)+1)^2 ≤ 2/(2*(n : ℝ)+1)-2/(2*(n : ℝ)+3) := by
  have h1 : 0 < (n : ℝ)+1/2 := by positivity
  have h2 : 0 < (n : ℝ)+3/2 := by positivity
  have he : (2 : ℝ)/(2*(n : ℝ)+1)-2/(2*(n : ℝ)+3) =
      1/(((n : ℝ)+1/2)*((n : ℝ)+3/2)) := by
    field_simp
    ring
  rw [he]
  exact one_div_le_one_div_of_le (mul_pos h1 h2) (by nlinarith)

end JSP233.StarMidpoint158375
