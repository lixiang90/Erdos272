module

public import Erdos272.Resources.NeighborMass208
public import Erdos272.Resources.UniformCapacity208

@[expose] public section

/-! The exact mixed uniform source pays the actual joint slot/triple mass. -/
namespace JSP233.NeighborJoint208
open StarCompletion SourceBridge208 PureSource208 IntrinsicTriples208 NeighborMass208
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem Q_mono_defect {s e f t : ℝ} (he : e ≤ f) (hs : 0 ≤ s-1-t) :
    Q s e t ≤ Q s f t := by
  have h1 := mul_le_mul_of_nonneg_right he hs
  have h2 : max (3*e-s-1) 0 ≤ max (3*f-s-1) 0 := max_le_max (by linarith only [he]) le_rfl
  have h3 : max (5*e-2*s-2) 0 ≤ max (5*f-2*s-2) 0 := max_le_max (by linarith only [he]) le_rfl
  have hm2 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 2)) (le_max_right (s-2-2*t) 0)
  have hm3 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right h3 (by norm_num : (0 : ℝ) ≤ 3)) (le_max_right (s-3-3*t) 0)
  unfold Q
  linarith only [h1, hm2, hm3]

theorem actual_Q_source {N e : ℕ} {S : Finset ℤ} {t : ℝ}
    (hN : 2 ≤ N) (hS : S ⊆ Ground N) (hs : 4 ≤ S.card) (ht : 0 ≤ t)
    (he : e ≤ Defect S) (hfirst : 0 ≤ (S.card : ℝ)-1-t) :
    Q S.card e t ≤ NeighborSlots208.Mass N (t/((N : ℝ)-1)) S := by
  apply le_trans (Q_mono_defect (s := (S.card : ℝ)) (e := (e : ℝ))
    (f := (Defect S : ℝ)) (t := t) (by exact_mod_cast he) hfirst)
  exact actual_Q_mass hN hS hs ht

def J (s e : ℕ) (v M : ℝ) : ℝ :=
  Q s e (7*v*M/25) + 160/(v*M)*(physicalK s e : ℝ)

/-- This uses the actual AP defect and the actual totient source expression.
No independently supplied neighbor-mass lower bound is a premise. -/
theorem actual_joint_source {N e : ℕ} {S : Finset ℤ} {v M : ℝ}
    (hN : 2 ≤ N) (hS : S ⊆ Ground N) (hs : 4 ≤ S.card)
    (hv : 0 < v) (hM : 0 < M) (he : e ≤ Defect S)
    (hfirst : 0 ≤ (S.card : ℝ)-1-7*v*M/25) :
    J S.card e v M ≤ UniformCapacity208.JointMass N v M S := by
  have hq := actual_Q_source hN hS hs (by positivity : 0 ≤ 7*v*M/25) he hfirst
  have hk : (physicalK S.card e : ℝ) ≤ (Pool S).card := by
    exact_mod_cast actual_source_of_defect (by omega : 2 ≤ S.card) he
  have hpaid := mul_le_mul_of_nonneg_left hk (show 0 ≤ 160/(v*M) by positivity)
  unfold J UniformCapacity208.JointMass
  exact add_le_add hq hpaid

#print axioms actual_Q_source
#print axioms actual_joint_source
end
end JSP233.NeighborJoint208
