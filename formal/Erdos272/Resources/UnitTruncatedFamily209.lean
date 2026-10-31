import Erdos272.Global.ActualUnitNearWindow208

namespace JSP233.UnitTruncatedFamily209
open StarCompletion APGeometry Density41
open SevenFamily208 UnitNearAggregate208 ActualUnitFees208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 200000

/-- Truncation keeps the actual original PoolNear family and all original
per-layer geometry. Only the first 150 true finite cleanup facts are used. -/
theorem actual_paid150 {N : ℕ} {A : Finset (Finset ℤ)} {g u eta light : ℝ}
    (hN : 659912≤N) (hNh : N≤705097)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,242≤S.card) (hsparse : ∀S∈A,11*S.card≤N)
    (hrows : ∀k,k<150→Facts242 k)
    (hg : 0≤g) (hrecip : 6*g*psi242 150=1)
    (harithmetic : 6*g*(∑k∈Finset.range 150,(psi242 (k+1)-psi242 k)*
      UnitFeeArithmetic208.upper242 N k)≤u*(N : ℝ)^2+eta*N+light) :
    UnitNearObligation N A g u eta light := by
  refine ⟨psi242,150,psi242_mono,psi242_zero,hrecip,?_⟩
  have hbill : ∀k,k<150→((PoolNear A psi242 k).card : ℝ)≤
      UnitFeeArithmetic208.upper242 N k := by
    intro k hk
    exact (ActualUnitFees208.actual_bill242 hN hNh hlegal hbad hsize hsparse k
      (by omega) (hrows k hk)).trans (ActualUnitNearWindow208.bill_upper242 N k (by omega))
  have hh:=Finset.sum_le_sum (s := Finset.range 150) (fun k hk=>
    mul_le_mul_of_nonneg_left (hbill k (Finset.mem_range.mp hk))
      (sub_nonneg.mpr (psi242_mono (Nat.le_succ k))))
  exact (mul_le_mul_of_nonneg_left hh (show 0≤6*g by positivity)).trans harithmetic

#print axioms actual_paid150
end
end JSP233.UnitTruncatedFamily209
