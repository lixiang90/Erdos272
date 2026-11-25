module

public import Erdos272.Resources.N67702.SourcePayment67702W10
public import Erdos272.Resources.N67702.SourcePayment67702W9

@[expose] public section

namespace JSP233.AmbientGround65968
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem ground_mono {N M : ℕ} (h : N≤M) : Ground N⊆Ground M := by
  intro x hx
  obtain ⟨hl,hu⟩ := (mem_ground N x).mp hx
  apply (mem_ground M x).mpr
  exact ⟨hl,hu.trans (by exact_mod_cast h)⟩
#print axioms ground_mono

theorem legal_mono {N M : ℕ} {F : Finset (Finset ℤ)}
    (h : N≤M) (hF : Legal (Ground N) F) : Legal (Ground M) F := by
  exact ⟨fun S hS => (hF.1 S hS).trans (ground_mono h),hF.2⟩
#print axioms legal_mono

theorem sparse_mono {N M : ℕ} {A : Finset (Finset ℤ)}
    (h : N≤M) (hs : ∀ S∈A, 12*S.card≤N) : ∀ S∈A, 12*S.card≤M :=
  fun S hS => (hs S hS).trans h
#print axioms sparse_mono
end
end JSP233.AmbientGround65968
