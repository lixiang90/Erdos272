module

public import Erdos272.Counting.N158375.DenseJoint158375
public import Erdos272.Capacity.N88404.SevenShadow88404

@[expose] public section

namespace JSP233.DenseJoint88404
open StarCompletion APGeometry DenseDeletion40 IntrinsicTriples208 HarmonicAbel29
open SieveConstants88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_AP_inner_with_deleted {N : ℕ} {A F : Finset (Finset ℤ)}
    {g Q : ℝ} (hlo : 15000≤N) (hhi : N≤2^18)
    (hF : Legal (Ground N) F) (hAF : A⊆F)
    (hsparse : ∀ S∈A, 12*S.card≤N) (hg : 0<g)
    (hpay : 1≤6*g*180200) (hcap : 3*g*((N-1 : ℕ) : ℝ)≤1)
    (hinner : (A.card : ℝ)≤6*g*(∑ S∈A, ((Pool S).card : ℝ))+Q) :
    ((F.filter IsAP).card : ℝ)+(A.card : ℝ)+((Deleted N 12 F).card : ℝ) ≤
      (129/800+3*g : ℝ)*(N : ℝ)^2+Alpha 1*g*((N-1 : ℕ) : ℝ)^3+
        1/(432*(Alpha 1*g)^2)+(N : ℝ)*Harmonic N+Q := by
  have hi := DenseJoint158375.actual_inner_payment_with_deleted hlo hhi hF hAF hsparse
    hg.le hpay hinner
  have hcast : ((N-1 : ℕ) : ℝ)=(N : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤N)]
    norm_num
  have hj := SevenShadow88404.actual_joint (by omega : 1000≤N) hg
    (by simpa only [hcast] using hcap) hF
  rw [←hcast] at hj
  linarith only [hi, hj]

#print axioms actual_AP_inner_with_deleted
end
end JSP233.DenseJoint88404
