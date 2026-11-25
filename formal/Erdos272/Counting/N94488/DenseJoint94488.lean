module

public import Erdos272.Counting.N158375.DenseJoint158375
public import Erdos272.Capacity.N94488.DoubleShadow94488

@[expose] public section

namespace JSP233.DenseJoint94488
open StarCompletion APGeometry DenseDeletion40 IntrinsicTriples208 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_AP_inner_with_deleted {N : ℕ} {A F : Finset (Finset ℤ)}
    {g Q : ℝ} (hlo : 15000 ≤ N) (hhi : N ≤ 2^18)
    (hF : Legal (Ground N) F) (hAF : A ⊆ F)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hg : 0 < g)
    (hpay : 1 ≤ 6*g*180200) (hcap : 4*g*((N-1 : ℕ) : ℝ) ≤ 1)
    (hinner : (A.card : ℝ) ≤ 6*g*(∑ S ∈ A, ((Pool S).card : ℝ))+Q) :
    ((F.filter IsAP).card : ℝ)+(A.card : ℝ)+((Deleted N 12 F).card : ℝ) ≤
      (129/800 : ℝ)*(N : ℝ)^2+(7*g/8)*((N-1 : ℕ) : ℝ)^3+
        73/(24000*g^2)+(N : ℝ)*Harmonic N+Q := by
  have hi := DenseJoint158375.actual_inner_payment_with_deleted hlo hhi hF hAF hsparse hg.le hpay hinner
  have hj := DoubleShadow94488.actual_joint (by omega : 2 ≤ N) hg hcap hF
  linarith only [hi, hj]

#print axioms actual_AP_inner_with_deleted
end
end JSP233.DenseJoint94488
