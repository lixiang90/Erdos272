module

public import Erdos272.Resources.NeighborSlots208
public import Erdos272.Resources.APResidual208
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! One weighted slot pool and one triple pool give the uniform capacity.
The three rank distances are not charged as independent physical pools. -/
namespace JSP233.UniformCapacity208
open StarCompletion IntrinsicTriples208 NeighborSlots208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def JointMass (N : ℕ) (v M : ℝ) (S : Finset ℤ) : ℝ :=
  Mass N ((7 * v * M / 25) / ((N : ℝ) - 1)) S +
    160 / (v * M) * (Pool S).card

theorem actual_slot_capacity {N : ℕ} {F : Finset (Finset ℤ)} {v M : ℝ}
    (hN : 2 ≤ N) (hv : 0 < v) (hM : 0 < M) (hF : Legal (Ground N) F) :
    (∑ S ∈ F, Mass N ((7 * v * M / 25) / ((N : ℝ) - 1)) S) ≤
      25 * (N : ℝ)^3 / (14 * v * M) := by
  have ht : 0 < 7 * v * M / 25 := by positivity
  have hh := NeighborSlots208.actual_capacity hN ht hF
  have hnum : (N : ℝ)^2 * (N - 1) ≤ (N : ℝ)^3 := by
    have hsq := sq_nonneg (N : ℝ)
    nlinarith only [hsq]
  have hdiv := div_le_div_of_nonneg_right hnum (show 0 ≤ 2 * (7 * v * M / 25) by positivity)
  apply hh.trans
  convert hdiv using 1 <;> field_simp <;> ring

theorem actual_triple_cube {N : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) : (∑ S ∈ F, ((Pool S).card : ℝ)) ≤ (N : ℝ)^3 / 6 := by
  have hc := IntrinsicTriples208.actual_capacity hF
  simp only [ground_card] at hc
  have hcR : (∑ S ∈ F, ((Pool S).card : ℝ)) ≤ (N.choose 3 : ℝ) := by exact_mod_cast hc
  have hh := APResidual208.choose_difference_cubic (a := 0) (n := N) (Nat.zero_le N)
  norm_num only [Nat.choose_zero_succ, Nat.cast_zero, zero_pow (by decide : 3 ≠ 0), sub_zero] at hh
  exact hcR.trans hh

theorem actual_joint_capacity {N : ℕ} {F : Finset (Finset ℤ)} {v M : ℝ}
    (hN : 2 ≤ N) (hv : 0 < v) (hM : 0 < M) (hF : Legal (Ground N) F) :
    (∑ S ∈ F, JointMass N v M S) ≤ 1195 * (N : ℝ)^3 / (42 * v * M) := by
  have hs := actual_slot_capacity hN hv hM hF
  have ht := mul_le_mul_of_nonneg_left (actual_triple_cube hF)
    (show 0 ≤ 160 / (v * M) by positivity)
  simp only [JointMass, Finset.sum_add_distrib, ← Finset.mul_sum]
  calc
    _ ≤ 25 * (N : ℝ)^3 / (14 * v * M) + 160 / (v * M) * ((N : ℝ)^3 / 6) := add_le_add hs ht
    _ = _ := by ring

#print axioms actual_slot_capacity
#print axioms actual_triple_cube
#print axioms actual_joint_capacity
end
end JSP233.UniformCapacity208
