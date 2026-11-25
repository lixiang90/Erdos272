module

public import Erdos272.Arithmetic.N180000.SharpPrime180000

@[expose] public section

namespace JSP233.PrimeSquareTail88404
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem centered_step {x : ℝ} (hx : 15 < x) :
    (1 : ℝ)/x^2 ≤ 1/(30*(x-15))-1/(30*(x+15)) := by
  have hleft : 0 < x-15 := by linarith only [hx]
  have hright : 0 < x+15 := by linarith only [hx]
  have he : (1 : ℝ)/(30*(x-15))-1/(30*(x+15)) = 1/((x-15)*(x+15)) := by
    field_simp [hleft.ne', hright.ne']
    ring
  rw [he]
  exact one_div_le_one_div_of_le (mul_pos hleft hright) (by nlinarith)

theorem tail_partial (a r : ℕ) (hr : 15 < r) :
    (∑ j ∈ Finset.range a, (1 : ℝ)/(30*(j : ℝ)+r)^2) ≤
      1/(30*((r : ℝ)-15))-1/(30*(30*(a : ℝ)+r-15)) := by
  have hrR : (15 : ℝ) < r := by exact_mod_cast hr
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ]
    have hs := centered_step (show (15 : ℝ) < 30*(a : ℝ)+r by
      nlinarith only [hrR, Nat.cast_nonneg (α := ℝ) a])
    have he : 30*((a+1 : ℕ) : ℝ)+r-15 = 30*(a : ℝ)+r+15 := by
      push_cast
      ring
    rw [he]
    linarith only [ih, hs]

theorem sum_bound (a r : ℕ) (hr : 15 < r) :
    (∑ j ∈ Finset.range a, (1 : ℝ)/(30*(j : ℝ)+r)^2) ≤ 1/(30*((r : ℝ)-15)) := by
  have hs := tail_partial a r hr
  have hrR : (15 : ℝ) < r := by exact_mod_cast hr
  have hp : 0 < 30*(a : ℝ)+r-15 := by
    nlinarith only [hrR, Nat.cast_nonneg (α := ℝ) a]
  have hn : (0 : ℝ) ≤ 1/(30*(30*(a : ℝ)+r-15)) := by positivity
  linarith only [hs, hn]

#print axioms centered_step
#print axioms tail_partial
#print axioms sum_bound
end
end JSP233.PrimeSquareTail88404
