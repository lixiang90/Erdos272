import Erdos272.Arithmetic.PrefixAbel208

namespace JSP233.LightPeriodic209
open PrefixAbel208
open scoped BigOperators
set_option maxHeartbeats 0

/-- A two-sided prefix discrepancy controls an increasing nonnegative weight.
The zero prefix is included, so the lower discrepancy is nonpositive. -/
theorem weighted_increasing (a w : ℕ→ℝ) (n : ℕ) (rho lo hi : ℝ)
    (hlo : lo≤0)
    (hprefix : ∀k, 1≤k → k≤n →
      rho*k+lo≤Prefix a k ∧ Prefix a k≤rho*k+hi)
    (hw : ∀i<n, 0≤w i)
    (hinc : ∀i, i+1<n → w i≤w (i+1)) :
    (∑i∈Finset.range n,a i*w i)≤
      rho*(∑i∈Finset.range n,w i)+(hi-lo)* (if n=0 then 0 else w (n-1)) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [abel_succ]
    have hh : Prefix a (n+1)*w n+
        (∑i∈Finset.range n,Prefix a (i+1)*(w i-w (i+1)))≤
        (rho*(n+1:ℕ)+hi)*w n+
        ∑i∈Finset.range n,(rho*(i+1:ℕ)+lo)*(w i-w (i+1)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (hprefix (n+1) (by omega) le_rfl).2
          (hw n (by omega))
      · apply Finset.sum_le_sum
        intro i hi'
        have hiN := Finset.mem_range.mp hi'
        exact mul_le_mul_of_nonpos_right (hprefix (i+1) (by omega) (by omega)).1
          (sub_nonpos.mpr (hinc i (by omega)))
    have ht := affine_telescope rho lo w n
    have hz : lo*w 0≤0 := mul_nonpos_of_nonpos_of_nonneg hlo (hw 0 (by omega))
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel] at *
    nlinarith only [hh,ht,hz]

#print axioms weighted_increasing
end JSP233.LightPeriodic209
