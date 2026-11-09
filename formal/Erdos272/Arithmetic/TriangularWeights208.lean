module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! A finite bound for triangular weights, proved by a square telescope. -/
namespace JSP233.TriangularWeights208
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def Weight (u : ℝ) (d : ℕ) : ℝ := max (1 - u * d) 0

theorem weight_nonneg (u : ℝ) (d : ℕ) : 0 ≤ Weight u d := le_max_right _ _

theorem square_step {u : ℝ} (hu : 0 ≤ u) (d : ℕ) :
    2 * u * Weight u (d + 1) ≤ (Weight u d)^2 - (Weight u (d + 1))^2 := by
  by_cases hh : 0 ≤ 1 - u * (d + 1 : ℕ)
  · have hp : 0 ≤ 1 - u * (d : ℝ) := by
      push_cast at hh
      nlinarith only [hh, hu]
    simp only [Weight, max_eq_left hh, max_eq_left hp]
    push_cast
    nlinarith only [sq_nonneg u]
  · have hz : Weight u (d + 1) = 0 := max_eq_right (by linarith only [hh])
    rw [hz]
    simpa only [mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] using sq_nonneg (Weight u d)

theorem square_telescope {u : ℝ} (hu : 0 ≤ u) (D : ℕ) :
    2 * u * (∑ d ∈ Finset.Icc 1 D, Weight u d) ≤ 1 - (Weight u D)^2 := by
  induction D with
  | zero => norm_num [Weight]
  | succ D ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ D + 1)]
    have hh := square_step hu D
    linarith only [ih, hh]

theorem weight_sum_bound {u : ℝ} (hu : 0 < u) (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, Weight u d) ≤ 1 / (2 * u) := by
  have hh := square_telescope hu.le D
  have hs := sq_nonneg (Weight u D)
  apply (le_div_iff₀ (by positivity : 0 < 2 * u)).mpr
  nlinarith only [hh, hs]

#print axioms square_telescope
#print axioms weight_sum_bound
end
end JSP233.TriangularWeights208
