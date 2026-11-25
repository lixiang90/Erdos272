module

public import Erdos272.Core.N94488.StarSmallKernel94488
public import Erdos272.Counting.N94488.DenseCount94488

@[expose] public section

namespace JSP233.StarStart94488
open StarCompletion APGeometry DenseDeletion40 StarStart233811
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 944880
theorem actual_retained_star_window {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hN : 94488≤N) (hhi : N≤179999)
    (hc : c∈Ground N) (hF : Legal (Ground N) F)
    (hroot : Rooted (Retained N 12 F) c) : F.card≤B N := by
  have hsub : Avoiders F c⊆Deleted N 12 F := by
    intro S hS
    obtain ⟨hSF,hcS⟩ := Finset.mem_filter.mp hS
    by_contra hnd
    exact hcS (hroot S (Finset.mem_sdiff.mpr ⟨hSF,hnd⟩))
  have hbad : ∀S∈Avoiders F c,¬IsAP S :=
    fun S hS => (Finset.mem_filter.mp (hsub hS)).2.1
  have hdel := DenseCount94488.actual_deleted_count (by omega : 90000≤N) (by omega : N ≤ 2^18) hF
  have hcount : (Avoiders F c).card≤86*N := (Finset.card_le_card hsub).trans hdel
  by_cases htwo : 2≤(Avoiders F c).card
  · by_cases hk : 2≤(CommonKernel (Ground N) F c).card
    · have hb := AnchorCompletion38.actual_crooked_large_kernel_payment N F c hc hF htwo hk hbad
      omega
    · exact StarSmallKernel94488.actual_small_kernel_window (by omega : 94488≤N) hhi hc hF htwo (by omega) hcount
  · apply AnchorCompletion38.actual_crooked_omitter_middle_window N F c (by omega) hc hF hbad
    omega


#print axioms actual_retained_star_window
end
end JSP233.StarStart94488
