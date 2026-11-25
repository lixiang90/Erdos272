module

public import Erdos272.Resources.N150465.SourcePayment150465W0

@[expose] public section

namespace JSP233.WindowPayment150465
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 SourceData150465W0
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_source_for_proof {N : ℕ} {A F : Finset (Finset ℤ)}
    (hlo : 150465 ≤ N) (hhi : N ≤ 153079)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 117 ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G*(∑ S ∈ F, ((Pool S).card : ℝ))+SourceUpper N :=
  SourcePayment150465W0.actual_source hlo hhi hlegal hbad hsize hsparse hAF

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment150465
