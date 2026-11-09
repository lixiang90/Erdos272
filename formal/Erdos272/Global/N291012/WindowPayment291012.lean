module

public import Erdos272.Resources.N291012.Layer291012
public import Erdos272.Resources.N291012.WindowData291012
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.WindowPayment291012
open StarCompletion APGeometry SevenFamily208 WindowData291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def Weighted (w : ℕ) : ℝ := 6*G w*(∑ i ∈ Finset.range 7,
  (Psi w (i+1)-Psi w i)*Layer291012.Upper (info w).high (7*w+i))

theorem fee00 : Weighted 0 ≤ (info 0).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info00, CleanupRows291012.data, CleanupRows291012.data00, CleanupRows291012.data01, CleanupRows291012.data02, CleanupRows291012.data03, CleanupRows291012.data04, CleanupRows291012.data05, CleanupRows291012.data06]
#print axioms fee00

theorem fee01 : Weighted 1 ≤ (info 1).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info01, CleanupRows291012.data, CleanupRows291012.data07, CleanupRows291012.data08, CleanupRows291012.data09, CleanupRows291012.data10, CleanupRows291012.data11, CleanupRows291012.data12, CleanupRows291012.data13]
#print axioms fee01

theorem fee02 : Weighted 2 ≤ (info 2).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info02, CleanupRows291012.data, CleanupRows291012.data14, CleanupRows291012.data15, CleanupRows291012.data16, CleanupRows291012.data17, CleanupRows291012.data18, CleanupRows291012.data19, CleanupRows291012.data20]
#print axioms fee02

theorem fee03 : Weighted 3 ≤ (info 3).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info03, CleanupRows291012.data, CleanupRows291012.data21, CleanupRows291012.data22, CleanupRows291012.data23, CleanupRows291012.data24, CleanupRows291012.data25, CleanupRows291012.data26, CleanupRows291012.data27]
#print axioms fee03

theorem fee04 : Weighted 4 ≤ (info 4).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info04, CleanupRows291012.data, CleanupRows291012.data28, CleanupRows291012.data29, CleanupRows291012.data30, CleanupRows291012.data31, CleanupRows291012.data32, CleanupRows291012.data33, CleanupRows291012.data34]
#print axioms fee04

theorem fee05 : Weighted 5 ≤ (info 5).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info05, CleanupRows291012.data, CleanupRows291012.data35, CleanupRows291012.data36, CleanupRows291012.data37, CleanupRows291012.data38, CleanupRows291012.data39, CleanupRows291012.data40, CleanupRows291012.data41]
#print axioms fee05

theorem fee06 : Weighted 6 ≤ (info 6).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info06, CleanupRows291012.data, CleanupRows291012.data42, CleanupRows291012.data43, CleanupRows291012.data44, CleanupRows291012.data45, CleanupRows291012.data46, CleanupRows291012.data47, CleanupRows291012.data48]
#print axioms fee06

theorem fee07 : Weighted 7 ≤ (info 7).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info07, CleanupRows291012.data, CleanupRows291012.data49, CleanupRows291012.data50, CleanupRows291012.data51, CleanupRows291012.data52, CleanupRows291012.data53, CleanupRows291012.data54, CleanupRows291012.data55]
#print axioms fee07

theorem fee08 : Weighted 8 ≤ (info 8).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info08, CleanupRows291012.data, CleanupRows291012.data56, CleanupRows291012.data57, CleanupRows291012.data58, CleanupRows291012.data59, CleanupRows291012.data60, CleanupRows291012.data61, CleanupRows291012.data62]
#print axioms fee08

theorem fee09 : Weighted 9 ≤ (info 9).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info09, CleanupRows291012.data, CleanupRows291012.data63, CleanupRows291012.data64, CleanupRows291012.data65, CleanupRows291012.data66, CleanupRows291012.data67, CleanupRows291012.data68, CleanupRows291012.data69]
#print axioms fee09

theorem fee10 : Weighted 10 ≤ (info 10).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info10, CleanupRows291012.data, CleanupRows291012.data70, CleanupRows291012.data71, CleanupRows291012.data72, CleanupRows291012.data73, CleanupRows291012.data74, CleanupRows291012.data75, CleanupRows291012.data76]
#print axioms fee10

theorem fee11 : Weighted 11 ≤ (info 11).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info11, CleanupRows291012.data, CleanupRows291012.data77, CleanupRows291012.data78, CleanupRows291012.data79, CleanupRows291012.data80, CleanupRows291012.data81, CleanupRows291012.data82, CleanupRows291012.data83]
#print axioms fee11

theorem fee12 : Weighted 12 ≤ (info 12).fee := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer291012.Upper, info, info12, CleanupRows291012.data, CleanupRows291012.data84, CleanupRows291012.data85, CleanupRows291012.data86, CleanupRows291012.data87, CleanupRows291012.data88, CleanupRows291012.data89, CleanupRows291012.data90]
#print axioms fee12

theorem fee {w : ℕ} (hw : w < 13) : Weighted w ≤ (info w).fee := by
  interval_cases w
  · exact fee00
  · exact fee01
  · exact fee02
  · exact fee03
  · exact fee04
  · exact fee05
  · exact fee06
  · exact fee07
  · exact fee08
  · exact fee09
  · exact fee10
  · exact fee11
  · exact fee12

theorem actual_obligation {N w : ℕ} {A : Finset (Finset ℤ)} (hw : w < 13)
    (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N) :
    UnitNearObligation N A (G w) 0 0 (info w).fee := by
  refine ⟨Psi w, 7, psi_mono hw, psi_zero w, reciprocal hw, ?_⟩
  have hs : (∑ i ∈ Finset.range 7, (Psi w (i+1)-Psi w i)*((PoolNear A (Psi w) i).card : ℝ)) ≤
      ∑ i ∈ Finset.range 7, (Psi w (i+1)-Psi w i)*Layer291012.Upper (info w).high (7*w+i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hl := links hw (Finset.mem_range.mp hi)
    have hb := Layer291012.actual_upper (N := N) (k := 7*w+i) (ell := i) (psi := Psi w) hl.1
      (by simpa only [hl.2.1] using hlo) (by simpa only [hl.2.2.1] using hhi) hlegal hbad
      (by simpa only [hl.2.2.2.1] using hsize) hsparse
      (by dsimp only [Psi]; exact_mod_cast hl.2.2.2.2)
    rw [hl.2.2.1] at hb
    exact mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr ((psi_mono hw) (Nat.le_succ i)))
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*G w by have hg := (gates hw).g_positive; positivity)
  have hf := fee hw
  dsimp only [Weighted] at hf
  simpa only [zero_mul, zero_add] using hp.trans hf

theorem actual_source {N w : ℕ} {A F : Finset (Finset ℤ)} (hw : w < 13)
    (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ F, ((IntrinsicTriples208.Pool S).card : ℝ))+(info w).fee := by
  have hb := SevenFamily208.actual_unit_source hAF (gates hw).g_positive.le
    (actual_obligation hw hlo hhi hlegal hbad hsize hsparse)
  simpa only [zero_mul, add_zero] using hb

#print axioms fee
#print axioms actual_obligation
#print axioms actual_source
end
end JSP233.WindowPayment291012
