module

public import Erdos272.Counting.N65968.AmbientGround65968

@[expose] public section

namespace JSP233.SourcePayment65172W7
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W10
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def SourceUpper (_N : ℕ) : ℝ := SourceData67702W10.SourceUpper 67702

theorem actual_inner_source {N : ℕ} {A F : Finset (Finset ℤ)}
    (hlo : 65172≤N) (hhi : N≤65967)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S∈A, ¬IsAP S)
    (hsize : ∀ S∈A, 101≤S.card) (hsparse : ∀ S∈A, 12*S.card≤N)
    (hlegalF : Legal (Ground N) F) (hAF : A⊆F) :
    (A.card : ℝ)≤6*G*(∑ S∈A, ((Pool S).card : ℝ))+SourceUpper N := by
  have hNM : N≤67702 := by omega
  exact SourcePayment67702W10.actual_inner_source (N:=67702)
    (by decide) (by decide) (AmbientGround65968.legal_mono hNM hlegal)
    hbad hsize (AmbientGround65968.sparse_mono hNM hsparse)
    (AmbientGround65968.legal_mono hNM hlegalF) hAF
#print axioms actual_inner_source
end
end JSP233.SourcePayment65172W7
