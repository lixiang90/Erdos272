import Mathlib.Tactic

/-! Exact finite Abel comparison with an affine prefix majorant. -/
namespace JSP233.PrefixAbel208
open scoped BigOperators
set_option maxHeartbeats 0

def Prefix (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, a i

theorem prefix_succ (a : ℕ → ℝ) (n : ℕ) : Prefix a (n+1) = Prefix a n+a n := by
  exact Finset.sum_range_succ a n

theorem abel_succ (a w : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), a i*w i) =
      Prefix a (n+1)*w n +
        ∑ i ∈ Finset.range n, Prefix a (i+1)*(w i-w (i+1)) := by
  induction n with
  | zero => simp [Prefix]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, prefix_succ a (n+1)]
    ring

theorem affine_telescope (delta C : ℝ) (w : ℕ → ℝ) (n : ℕ) :
    (delta*(n+1 : ℕ)+C)*w n +
      (∑ i ∈ Finset.range n, (delta*(i+1 : ℕ)+C)*(w i-w (i+1))) =
      delta*(∑ i ∈ Finset.range (n+1), w i)+C*w 0 := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast at ih ⊢
    nlinarith only [ih]

/-- One affine prefix bound pays every nonnegative decreasing weight. -/
theorem weighted_upper (a w : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (delta C : ℝ)
    (hprefix : ∀ k, 1 ≤ k → k ≤ n → Prefix a k ≤ delta*k+C)
    (hw : ∀ i < n, 0 ≤ w i)
    (hdec : ∀ i, i+1 < n → w (i+1) ≤ w i) :
    (∑ i ∈ Finset.range n, a i*w i) ≤
      delta*(∑ i ∈ Finset.range n, w i)+C*w 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [abel_succ]
  calc
    _ ≤ (delta*(k+1 : ℕ)+C)*w k +
        ∑ i ∈ Finset.range k, (delta*(i+1 : ℕ)+C)*(w i-w (i+1)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (hprefix (k+1) (by omega) le_rfl) (hw k (by omega))
      · apply Finset.sum_le_sum
        intro i hi
        have hik := Finset.mem_range.mp hi
        exact mul_le_mul_of_nonneg_right (hprefix (i+1) (by omega) (by omega))
          (sub_nonneg.mpr (hdec i (by omega)))
    _ = _ := affine_telescope delta C w k

#print axioms abel_succ
#print axioms weighted_upper
end JSP233.PrefixAbel208
