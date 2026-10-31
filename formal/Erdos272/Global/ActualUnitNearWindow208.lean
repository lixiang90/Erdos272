import Erdos272.Resources.ActualUnitFees208
import Erdos272.Arithmetic.UnitFeeArithmetic208
import Erdos272.Global.HybridGlobal208

namespace JSP233.ActualUnitNearWindow208
open StarCompletion APGeometry Density41
open SevenFamily208 SevenPrices208 UnitNearAggregate208 ActualUnitFees208
open ResidualTable208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 200000

theorem bill_upper242 (N k : ℕ) (hk : k<183) : Bill242 N k≤UnitFeeArithmetic208.upper242 N k := by
  by_cases hk0 : k=0
  · subst k
    rw [UnitFeeArithmetic208.upper242_zero]
    change (0 : ℝ)≤0
    exact le_rfl
  · have h2 : 2≤k+1 := by omega
    have hr := ResidualTable208.bound242 (k+1) (by omega) (by omega)
    rw [ResidualCeil208.B,if_pos h2] at hr
    norm_num only [ResidualCeil208.Grid] at hr
    have hp := mul_le_mul_of_nonneg_left hr (sq_nonneg (N : ℝ))
    simp only [Bill242,Bill,if_neg hk0,UnitFeeArithmetic208.upper242,UnitFeeArithmetic208.upper,if_neg hk0]
    linarith only [hp]

theorem bill_upper243 (N k : ℕ) (hk : k<184) : Bill243 N k≤UnitFeeArithmetic208.upper243 N k := by
  by_cases hk0 : k=0
  · subst k
    rw [UnitFeeArithmetic208.upper243_zero]
    change (0 : ℝ)≤0
    exact le_rfl
  · have h2 : 2≤k+1 := by omega
    have hr := ResidualTable208.bound243 (k+1) (by omega) (by omega)
    rw [ResidualCeil208.B,if_pos h2] at hr
    norm_num only [ResidualCeil208.Grid] at hr
    have hp := mul_le_mul_of_nonneg_left hr (sq_nonneg (N : ℝ))
    simp only [Bill243,Bill,if_neg hk0,UnitFeeArithmetic208.upper243,UnitFeeArithmetic208.upper,if_neg hk0]
    linarith only [hp]

theorem actual_paid242 {N : ℕ} {A : Finset (Finset ℤ)} (hN : 659912≤N) (hNh : N≤705097)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,242≤S.card) (hsparse : ∀S∈A,11*S.card≤N)
    (hrows : ∀k,k<183→Facts242 k) : UnitNearObligation N A G242 U242 Eta242 Light242 := by
  have hh := Finset.sum_le_sum (s := Finset.range 183) (fun k hk=>
    mul_le_mul_of_nonneg_left (bill_upper242 N k (Finset.mem_range.mp hk))
      (sub_nonneg.mpr (psi242_mono (Nat.le_succ k))))
  have hs := mul_le_mul_of_nonneg_left hh (by norm_num [G242] : 0≤6*G242)
  have hn : 6*G242*(∑k∈Finset.range 183,(psi242 (k+1)-psi242 k)*UnitFeeArithmetic208.upper242 N k)≤
      U242*(N : ℝ)^2+Eta242*N+Light242 := by
    simpa only [psi242_eq] using UnitFeeArithmetic208.weighted_upper242 N
  exact ActualUnitFees208.actual_unit242 hN hNh hlegal hbad hsize hsparse hrows (hs.trans hn)

theorem actual_paid243 {N : ℕ} {A : Finset (Finset ℤ)} (hN : 659912≤N) (hNh : N≤705097)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,243≤S.card) (hsparse : ∀S∈A,11*S.card≤N)
    (hrows : ∀k,k<184→Facts243 k) : UnitNearObligation N A G243 U243 Eta243 Light243 := by
  have hh := Finset.sum_le_sum (s := Finset.range 184) (fun k hk=>
    mul_le_mul_of_nonneg_left (bill_upper243 N k (Finset.mem_range.mp hk))
      (sub_nonneg.mpr (psi243_mono (Nat.le_succ k))))
  have hs := mul_le_mul_of_nonneg_left hh (by norm_num [G243] : 0≤6*G243)
  have hn : 6*G243*(∑k∈Finset.range 184,(psi243 (k+1)-psi243 k)*UnitFeeArithmetic208.upper243 N k)≤
      U243*(N : ℝ)^2+Eta243*N+Light243 := by
    simpa only [psi243_eq] using UnitFeeArithmetic208.weighted_upper243 N
  exact ActualUnitFees208.actual_unit243 hN hNh hlegal hbad hsize hsparse hrows (hs.trans hn)

theorem actual_fees {N : ℕ} {F : Finset (Finset ℤ)} (hN : 659912≤N) (hNh : N≤705097)
    (hF : Legal (Ground N) F) (hrows242 : ∀k,k<183→Facts242 k) (hrows243 : ∀k,k<184→Facts243 k) :
    HybridGlobal208.UnitNearFees N (SparseCrooked N 11 F) := by
  have hsub := actual_sparse_subset N 11 F
  constructor
  · intro A hA hs
    exact actual_paid242 hN hNh
      ⟨fun S hS=>hF.1 S (hsub (hA hS)),fun S hS T hT hST=>hF.2 S (hsub (hA hS)) T (hsub (hA hT)) hST⟩
      (fun S hS=>(actual_sparse_membership.mp (hA hS)).2.1) hs
      (fun S hS=>(actual_sparse_membership.mp (hA hS)).2.2) hrows242
  · intro A hA hs
    exact actual_paid243 hN hNh
      ⟨fun S hS=>hF.1 S (hsub (hA hS)),fun S hS T hT hST=>hF.2 S (hsub (hA hS)) T (hsub (hA hT)) hST⟩
      (fun S hS=>(actual_sparse_membership.mp (hA hS)).2.1) hs
      (fun S hS=>(actual_sparse_membership.mp (hA hS)).2.2) hrows243

theorem actual_original_upper {N : ℕ} {F : Finset (Finset ℤ)} (hN : 659912≤N) (hNh : N≤705097)
    (hF : Legal (Ground N) F) (hrows242 : ∀k,k<183→Facts242 k) (hrows243 : ∀k,k<184→Facts243 k) :
    F.card≤B N := HybridGlobal208.actual_original_upper hN hNh hF (actual_fees hN hNh hF hrows242 hrows243)

#print axioms bill_upper242
#print axioms bill_upper243
#print axioms actual_paid242
#print axioms actual_paid243
#print axioms actual_fees
#print axioms actual_original_upper
end
end JSP233.ActualUnitNearWindow208
