module

public import Erdos272.Core.N67702.FixedAnchorSmall67702
public import Erdos272.Counting.N67702.SmallGates67702

@[expose] public section

namespace JSP233.SmallCredit67702
open StarCompletion SparseSmall39 SmallKernel112 SmallData67702
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_small_policy_credit {N p : ℕ} {F : Finset (Finset ℤ)}
    (hp : p<8) (hN : (policy p).low≤N)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F, ¬IsAP S)
    (hsmall : (Small F (policy p).T).Nonempty)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F (policy p).L)=∅) :
    (F.card : ℝ)≤((policy p).coefficient : ℝ)*N-(policy p).credit := by
  have hg := SmallGates67702.gates hp
  have hlo := hg.low_bound.trans hN
  have hlength := hg.length_upper
  have htwo : 2*(policy p).L+1≤N := by omega
  have hsquare : ((policy p).L-1)^2≤83^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hfloor := Nat.div_le_div_right (c := 4) hsquare
  have hgap : (policy p).L+1+((policy p).L-1)^2/4≤N := by omega
  have hb := FixedAnchorSmall67702.actual_fixed_anchor_small_credit
    hg.length_lower hg.T_le_L htwo hgap hlegal hbad hsmall hkernel
  rw [←hg.coefficient_eq,←hg.credit_eq] at hb
  exact hb

#print axioms actual_small_policy_credit
end
end JSP233.SmallCredit67702
