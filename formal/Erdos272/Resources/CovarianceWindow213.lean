module

public import Erdos272.Resources.CovarianceResource213
public import Erdos272.Arithmetic.TotientWindow209
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Actual finite-frontier instantiation: no numerical-bound or covariance
moment assumption remains in the two resource APIs below. -/
namespace JSP233.CovarianceWindow213
open MiddleJoint51 LocalizedMiddle208 FrontierDensity208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem finite_frontiers {N : ℕ} (hN : N≤720896) :
    (∀t≤N,Rho*t-17/200≤TotientRows208.TotientMass t) ∧
    (∀t≤N,TotientRows208.TotientMass t≤(76/125 : ℝ)*t+579/1000) ∧
    (∀t≤N,Rho*(t : ℝ)^2/2-(61/200)*t≤TotientTriangle t) := by
  refine ⟨?_,?_,?_⟩
  · intro t ht
    simpa only [Rho,TotientRows208.TotientMass] using
      (TotientWindow209.bounds t (ht.trans hN)).1
  · intro t ht
    simpa only [TotientRows208.TotientMass] using TotientWindow209.mass_upper t (ht.trans hN)
  · intro t ht
    simpa only [Rho,TotientTriangle] using (TotientWindow209.bounds t (ht.trans hN)).2

theorem actual_resource_sum_slack {N c L R : ℕ}
    (hL : 1≤L) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N) (hN : N≤720896)
    (e : ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧e d≤(R-c)/d) :
    ((∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℕ) : ℝ)+3≤
      (R : ℝ)^2/2-CovarianceScalar213.K*L^2+
        (L : ℝ)*CovarianceScalar213.Polynomial (Real.log L)+850 := by
  obtain ⟨hF,hFu,hU⟩:=finite_frontiers hN
  exact CovarianceResource213.actual_resource_sum_slack
    hL hcL hLR hRN (by omega) e he hF hFu hU

theorem actual_middle_profile {N c L R : ℕ}
    (hL : 1≤L) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N) (hN : N≤720896)
    (e : ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧e d≤(R-c)/d) :
    ((R : ℝ)+(129/200)*L)*(N-R)+
      ((∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℕ) : ℝ)≤
        (N : ℝ)^2/2-RawEndpoint115.ProfileDeficit L (N-R)+
          (L : ℝ)*CovarianceScalar213.Polynomial (Real.log L)+850 := by
  obtain ⟨hF,hFu,hU⟩:=finite_frontiers hN
  exact CovarianceResource213.actual_middle_profile
    hL hcL hLR hRN (by omega) e he hF hFu hU

#print axioms finite_frontiers
#print axioms actual_resource_sum_slack
#print axioms actual_middle_profile
end
end JSP233.CovarianceWindow213
