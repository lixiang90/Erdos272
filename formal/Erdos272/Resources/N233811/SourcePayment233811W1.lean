module

public import Erdos272.Resources.N233811.Layer233811
public import Erdos272.Resources.N233811.SourceData233811W1
public import Erdos272.Resources.N291012.LowResourceBridges3040
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.SourcePayment233811W1
open StarCompletion APGeometry SevenFamily208 SourceData233811W1
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Weighted (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 5,
  (Psi (i+1)-Psi i)*Layer233811.Upper N (7+i))

theorem fee (N : ℕ) : Weighted N = SourceUpper N := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer233811.Upper, CleanupRows233811.data,
    CleanupRows233811.data00, CleanupRows233811.data01, CleanupRows233811.data02, CleanupRows233811.data03, CleanupRows233811.data04, CleanupRows233811.data05, CleanupRows233811.data06, CleanupRows233811.data07, CleanupRows233811.data08, CleanupRows233811.data09, CleanupRows233811.data10, CleanupRows233811.data11, SourceUpper, CoeffA, CoeffB, CoeffC]
  ring

theorem actual_obligation {N : ℕ} {A : Finset (Finset ℤ)}
    (hlo : 241006 ≤ N) (hhi : N ≤ 246006)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 147 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N) :
    UnitNearObligation N A G CoeffA CoeffB CoeffC := by
  refine ⟨Psi, 5, psi_mono, psi_zero, reciprocal, ?_⟩
  have hs : (∑ i ∈ Finset.range 5, (Psi (i+1)-Psi i)*((PoolNear A Psi i).card : ℝ)) ≤
      ∑ i ∈ Finset.range 5, (Psi (i+1)-Psi i)*Layer233811.Upper N (7+i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi5 := Finset.mem_range.mp hi
    have hl := links hi5
    have hb := Layer233811.actual_upper (N := N) (k := 7+i) (ell := i) (psi := Psi)
      (by omega : 7+i < 12) (by simpa only [hl.1] using hlo)
      (by simpa only [hl.2.1] using hhi) hlegal hbad
      (by simpa only [hl.2.2.1] using hsize) hsparse
      (by dsimp only [Psi]; exact_mod_cast hl.2.2.2)
    exact mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr (psi_mono (Nat.le_succ i)))
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*G by have h := g_positive; positivity)
  change _ ≤ SourceUpper N
  exact hp.trans_eq (fee N)

theorem actual_source {N : ℕ} {A F : Finset (Finset ℤ)}
    (hlo : 241006 ≤ N) (hhi : N ≤ 246006)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 147 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G*(∑ S ∈ F, ((IntrinsicTriples208.Pool S).card : ℝ))+SourceUpper N := by
  have hb := SevenFamily208.actual_unit_source hAF g_positive.le
    (actual_obligation hlo hhi hlegal hbad hsize hsparse)
  simpa only [SourceUpper, add_assoc] using hb

#print axioms fee
#print axioms actual_obligation
#print axioms actual_source
end
end JSP233.SourcePayment233811W1
