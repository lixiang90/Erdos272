module

public import Erdos272.Resources.N250262.Layer250262
public import Erdos272.Resources.N250262.SourceWindowData250262
public import Erdos272.Resources.N250262.WindowData250262
public import Erdos272.Resources.N291012.LowResourceBridges3040
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.WindowPayment250262
open StarCompletion APGeometry SevenFamily208 SourceWindowData250262
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Weighted (w : ℕ) : ℝ := 6*G w*(∑ i ∈ Finset.range 7,
  (Psi w (i+1)-Psi w i)*Layer250262.Upper (info w).high (7*w+i))

theorem fee00 : Weighted 0 ≤ (info 0).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer250262.Upper, info, info00, CleanupRows250262.data, CleanupRows250262.data00, CleanupRows250262.data01, CleanupRows250262.data02, CleanupRows250262.data03, CleanupRows250262.data04, CleanupRows250262.data05, CleanupRows250262.data06]
#print axioms fee00

theorem fee01 : Weighted 1 ≤ (info 1).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer250262.Upper, info, info01, CleanupRows250262.data, CleanupRows250262.data07, CleanupRows250262.data08, CleanupRows250262.data09, CleanupRows250262.data10, CleanupRows250262.data11, CleanupRows250262.data12, CleanupRows250262.data13]
#print axioms fee01

theorem fee02 : Weighted 2 ≤ (info 2).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer250262.Upper, info, info02, CleanupRows250262.data, CleanupRows250262.data14, CleanupRows250262.data15, CleanupRows250262.data16, CleanupRows250262.data17, CleanupRows250262.data18, CleanupRows250262.data19, CleanupRows250262.data20]
#print axioms fee02

theorem fee03 : Weighted 3 ≤ (info 3).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer250262.Upper, info, info03, CleanupRows250262.data, CleanupRows250262.data21, CleanupRows250262.data22, CleanupRows250262.data23, CleanupRows250262.data24, CleanupRows250262.data25, CleanupRows250262.data26, CleanupRows250262.data27]
#print axioms fee03

theorem fee {w : ℕ} (hw : w < 4) : Weighted w ≤ (info w).fee := by
  interval_cases w
  · exact fee00
  · exact fee01
  · exact fee02
  · exact fee03

theorem actual_obligation {N w : ℕ} {A : Finset (Finset ℤ)} (hw : w < 4)
    (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N) :
    UnitNearObligation N A (G w) 0 0 (info w).fee := by
  refine ⟨Psi w, 7, psi_mono hw, psi_zero w, reciprocal hw, ?_⟩
  have hs : (∑ i ∈ Finset.range 7, (Psi w (i+1)-Psi w i)*((PoolNear A (Psi w) i).card : ℝ)) ≤
      ∑ i ∈ Finset.range 7, (Psi w (i+1)-Psi w i)*Layer250262.Upper (info w).high (7*w+i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hl := links hw (Finset.mem_range.mp hi)
    have hb := Layer250262.actual_upper (N := N) (k := 7*w+i) (ell := i) (psi := Psi w) hl.1
      (by simpa only [hl.2.1] using hlo) (by simpa only [hl.2.2.1] using hhi) hlegal hbad
      (by simpa only [hl.2.2.2.1] using hsize) hsparse
      (by dsimp only [Psi]; exact_mod_cast hl.2.2.2.2)
    rw [hl.2.2.1] at hb
    exact mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr ((psi_mono hw) (Nat.le_succ i)))
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*G w by have hg := (g_positive hw); positivity)
  have hf := fee hw
  dsimp only [Weighted] at hf
  simpa only [zero_mul, zero_add] using hp.trans hf

theorem actual_source {N w : ℕ} {A F : Finset (Finset ℤ)} (hw : w < 4)
    (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ F, ((IntrinsicTriples208.Pool S).card : ℝ))+(info w).fee := by
  have hb := SevenFamily208.actual_unit_source hAF (g_positive hw).le
    (actual_obligation hw hlo hhi hlegal hbad hsize hsparse)
  simpa only [zero_mul, add_zero] using hb


theorem actual_source_for_proof {N w : ℕ} {A F : Finset (Finset ℤ)}
    (hw : w < 5) (hhi : N ≤ (WindowData250262.info w).high)
    (_hF : Legal (Ground N) F) (hlegal : Legal (Ground N) A)
    (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (WindowData250262.info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*WindowData250262.G w*
      (∑ S ∈ F, ((IntrinsicTriples208.Pool S).card : ℝ))+(WindowData250262.info w).fee := by
  have hl := WindowData250262.links hw
  have hbound := hhi.trans hl.2.2.2
  have hsize' : ∀ S ∈ A, (info (WindowData250262.sourceIndex w)).memberFloor ≤ S.card := by
    simpa only [hl.2.1] using hsize
  by_cases hlo : (info (WindowData250262.sourceIndex w)).low ≤ N
  · have h := actual_source hl.1 hlo hbound hlegal hbad hsize' hsparse hAF
    simpa only [WindowData250262.G, hl.2.2.1] using h
  · have hn : N ≤ (info (WindowData250262.sourceIndex w)).low := by omega
    have h := actual_source hl.1 le_rfl (intervals hl.1).1
      (LowResourceBridges3040.legal_ambient hn hlegal) hbad hsize'
      (fun S hS => (hsparse S hS).trans hn) hAF
    simpa only [WindowData250262.G, hl.2.2.1] using h

#print axioms fee
#print axioms actual_obligation
#print axioms actual_source
#print axioms actual_source_for_proof
end
end JSP233.WindowPayment250262
