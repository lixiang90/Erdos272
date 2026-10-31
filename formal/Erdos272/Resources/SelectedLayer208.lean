import Erdos272.Resources.LayerPayment208
namespace JSP233.SelectedLayer208
open scoped BigOperators
set_option maxHeartbeats 0
/-- Sampling the monotone source potential permits the seven selected
thresholds of the cost recipe, without charging every intermediate layer. -/
theorem sampled_pointwise_cover (psi : ℕ → ℝ) (nodes : ℕ → ℕ)
    (hpsi : Monotone psi) (hnodes : Monotone nodes) (n e : ℕ) (mass : ℝ)
    (hzero : psi (nodes 0) ≤ mass)
    (hpast : ∀ j ≤ n, nodes j ≤ e → psi (nodes j) ≤ mass) :
    psi (nodes n) ≤ mass + ∑ j ∈ Finset.range n,
      (psi (nodes (j+1)) - psi (nodes j)) * (if e < nodes (j+1) then 1 else 0) := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    have hprev := ih (fun j hj he => hpast j (by omega) he)
    rw [Finset.sum_range_succ]
    by_cases he : e < nodes (n+1)
    · simp only [if_pos he, mul_one]
      linarith only [hprev]
    · have hp := hpast (n+1) le_rfl (by omega)
      have hsum : 0 ≤ ∑ j ∈ Finset.range n,
          (psi (nodes (j+1)) - psi (nodes j)) *
            (if e < nodes (j+1) then 1 else 0) := by
        apply Finset.sum_nonneg
        intro j _
        apply mul_nonneg (sub_nonneg.mpr (hpsi (hnodes (by omega))))
        split_ifs <;> norm_num
      simp only [if_neg he, mul_zero, add_zero]
      linarith only [hp, hsum]

#print axioms sampled_pointwise_cover
end JSP233.SelectedLayer208
