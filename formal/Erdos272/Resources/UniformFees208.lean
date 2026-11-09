module

public import Erdos272.Resources.UniformCapacity208
public import Erdos272.Resources.LayerPayment208
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Every complete uniform layer pays the same actual mixed resource once. -/
namespace JSP233.UniformFees208
open StarCompletion IntrinsicTriples208 UniformCapacity208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem pointwise_cover (psi : ℕ→ℝ) (hpsi : Monotone psi) (near : ℕ→Prop)
    [DecidablePred near] (cap : ℕ) (mass : ℝ) (hzero : psi 0≤mass)
    (hfar : ∀ i<cap,¬near i →psi (i+1)≤mass) :
    psi cap≤mass+∑ i∈Finset.range cap,(psi (i+1)-psi i)*(if near i then 1 else 0) := by
  induction cap with
  | zero => simpa using hzero
  | succ cap ih =>
    have hprev := ih (fun i hi=>hfar i (by omega))
    rw [Finset.sum_range_succ]
    by_cases hn : near cap
    · simp only [if_pos hn,mul_one]
      linarith only [hprev]
    · have hp := hfar cap (by omega) hn
      have hs : 0≤∑ i∈Finset.range cap,(psi (i+1)-psi i)*(if near i then 1 else 0) := by
        apply Finset.sum_nonneg
        intro i hi
        apply mul_nonneg (sub_nonneg.mpr (hpsi (Nat.le_succ i)))
        split_ifs <;> norm_num
      simp only [if_neg hn,mul_zero,add_zero]
      linarith only [hp,hs]

theorem joint_nonneg {N : ℕ} {v M : ℝ} (hv : 0<v) (hM : 0<M) (S : Finset ℤ) :
    0≤JointMass N v M S := by
  unfold JointMass NeighborSlots208.Mass
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro x hx
    exact TriangularWeights208.weight_nonneg _ _
  · positivity

theorem family_resource {N : ℕ} {A : Finset (Finset ℤ)} {v M : ℝ}
    (hv : 0<v) (hM : 0<M) (psi : ℕ→ℝ) (hpsi : Monotone psi) (hz : psi 0=0)
    (near : ℕ→Finset (Finset ℤ)) (fee : ℕ→ℝ) (cap : ℕ)
    (hsub : ∀ i<cap,near i⊆A) (hfee : ∀ i<cap,((near i).card : ℝ)≤fee i)
    (hfar : ∀ S∈A,∀ i<cap,S∉near i →v^2*psi (i+1)≤JointMass N v M S) :
    v^2*psi cap*A.card≤(∑ S∈A,JointMass N v M S)+
      v^2*(∑ i∈Finset.range cap,(psi (i+1)-psi i)*fee i) := by
  have hcover : ∀ S∈A,v^2*psi cap≤JointMass N v M S+
      ∑ i∈Finset.range cap,(v^2*psi (i+1)-v^2*psi i)*(if S∈near i then 1 else 0) := by
    intro S hS
    exact pointwise_cover (fun i=>v^2*psi i) (fun i j hij=>mul_le_mul_of_nonneg_left (hpsi hij) (sq_nonneg v))
      (fun i=>S∈near i) cap _ (by rw [hz,mul_zero];exact joint_nonneg hv hM S) (hfar S hS)
  have hh := LayerPayment208.fractional_cover A (Finset.range cap) near (JointMass N v M)
    (fun i=>v^2*psi (i+1)-v^2*psi i) (v^2*psi cap)
    (fun i hi=>hsub i (Finset.mem_range.mp hi)) hcover
  have hf : (∑ i∈Finset.range cap,(v^2*psi (i+1)-v^2*psi i)*((near i).card : ℝ))≤
      v^2*(∑ i∈Finset.range cap,(psi (i+1)-psi i)*fee i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hh := mul_le_mul_of_nonneg_left (hfee i (Finset.mem_range.mp hi))
      (mul_nonneg (sq_nonneg v) (sub_nonneg.mpr (hpsi (Nat.le_succ i))))
    nlinarith only [hh]
  linarith only [hh,hf]

theorem family_capacity {N : ℕ} {A F : Finset (Finset ℤ)} {v M : ℝ}
    (hN : 2≤N) (hv : 0<v) (hM : 0<M) (hF : Legal (Ground N) F) (hAF : A⊆F)
    (psi : ℕ→ℝ) (hpsi : Monotone psi) (hz : psi 0=0)
    (near : ℕ→Finset (Finset ℤ)) (fee : ℕ→ℝ) (cap : ℕ)
    (hsub : ∀ i<cap,near i⊆A) (hfee : ∀ i<cap,((near i).card : ℝ)≤fee i)
    (hfar : ∀ S∈A,∀ i<cap,S∉near i →v^2*psi (i+1)≤JointMass N v M S) :
    v^2*psi cap*A.card≤1195*(N : ℝ)^3/(42*v*M)+
      v^2*(∑ i∈Finset.range cap,(psi (i+1)-psi i)*fee i) := by
  have hh := family_resource hv hM psi hpsi hz near fee cap hsub hfee hfar
  have hs : (∑ S∈A,JointMass N v M S)≤∑ S∈F,JointMass N v M S :=
    Finset.sum_le_sum_of_subset_of_nonneg hAF (fun S hS hnot=>joint_nonneg hv hM S)
  have hc := actual_joint_capacity hN hv hM hF
  linarith only [hh,hs,hc]

theorem family_price {N : ℕ} {A F : Finset (Finset ℤ)} {v M : ℝ}
    (hN : 2≤N) (hv : 0<v) (hM : 0<M) (hF : Legal (Ground N) F) (hAF : A⊆F)
    (psi : ℕ→ℝ) (hpsi : Monotone psi) (hz : psi 0=0)
    (near : ℕ→Finset (Finset ℤ)) (fee : ℕ→ℝ) (cap : ℕ) (hcap : 0<psi cap)
    (hsub : ∀ i<cap,near i⊆A) (hfee : ∀ i<cap,((near i).card : ℝ)≤fee i)
    (hfar : ∀ S∈A,∀ i<cap,S∉near i →v^2*psi (i+1)≤JointMass N v M S) :
    (A.card : ℝ)≤1195/(42*M*psi cap)*(N : ℝ)^3/v^3+
      (∑ i∈Finset.range cap,(psi (i+1)-psi i)*fee i)/(psi cap) := by
  have hh := family_capacity hN hv hM hF hAF psi hpsi hz near fee cap hsub hfee hfar
  have hden : 0<v^2*psi cap := by positivity
  apply (mul_le_mul_iff_right₀ hden).mp
  have he : (v^2*psi cap)*(1195/(42*M*psi cap)*(N : ℝ)^3/v^3+
      (∑ i∈Finset.range cap,(psi (i+1)-psi i)*fee i)/(psi cap))=
      1195*(N : ℝ)^3/(42*v*M)+v^2*(∑ i∈Finset.range cap,(psi (i+1)-psi i)*fee i) := by
    field_simp
    <;> ring
  rw [he]
  exact hh

#print axioms pointwise_cover
#print axioms family_resource
#print axioms family_capacity
#print axioms family_price
end
end JSP233.UniformFees208
