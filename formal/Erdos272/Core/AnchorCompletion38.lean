import Erdos272.Geometry.AnchorGeometry38
import Erdos272.Core.MiddleWindow32

/-! Actual two-point capacity and original-[N] conclusions after discharging
the common-point theorem.  No auxiliary trace or StarBound premise is exposed. -/
namespace JSP233.AnchorCompletion38
open StarCompletion AnchorGeometry38
open scoped Classical
noncomputable section

theorem actual_two_point_crooked_capacity (Ω : Finset ℤ) (D : Finset (Finset ℤ)) (u v : ℤ)
    (huv : u≠v) (hD : D.Nonempty) (hlegal : Legal Ω D)
    (hbad : ∀ S∈D, ¬IsAP S) (hu : ∀ S∈D, u∈S) (hv : ∀ S∈D, v∈S) :
    D.card+2≤(D.biUnion id).card := by
  have hk : ({u,v}:Finset ℤ).card=2 := by simp [huv]
  have hanchor : ∀ S∈D, ({u,v}:Finset ℤ)⊆S := by
    intro S hS x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu S hS
    · have he : x=v := Finset.mem_singleton.mp hx
      exact he ▸ hv S hS
  have hh := actual_arbitrary_AP_anchor_capacity Ω {u,v} D (pair_isAP u v)
    (by omega) hD hlegal hbad hanchor
  simpa only [hk] using hh

theorem actual_two_point_crooked_ground_capacity (Ω : Finset ℤ) (D : Finset (Finset ℤ)) (u v : ℤ)
    (huv : u≠v) (hD : D.Nonempty) (hlegal : Legal Ω D)
    (hbad : ∀ S∈D, ¬IsAP S) (hu : ∀ S∈D, u∈S) (hv : ∀ S∈D, v∈S) :
    D.card+2≤Ω.card := by
  apply (actual_two_point_crooked_capacity Ω D u v huv hD hlegal hbad hu hv).trans
  apply Finset.card_le_card
  intro x hx
  obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hx
  exact hlegal.1 S hS hxS

theorem actual_crooked_large_kernel_payment (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (hm : 2≤(Avoiders F c).card) (hk : 2≤(CommonKernel (Ground N) F c).card)
    (hbad : ∀ S∈Avoiders F c, ¬IsAP S) : F.card+1≤B N := by
  exact general_crooked_avoiders_payment (Ground N) F c (B N) hc hlegal
    (StarBoundConcrete30.actual_starBound N) hm hk hbad

theorem actual_crooked_omitter_middle_window (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hN : 65536≤N) (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈Avoiders F c, ¬IsAP S)
    (hcount : (Avoiders F c).card≤2*N-6) : F.card≤B N := by
  by_cases hm : 2≤(Avoiders F c).card
  · by_cases hk : 2≤(CommonKernel (Ground N) F c).card
    · have hh := actual_crooked_large_kernel_payment N F c hc hlegal hm hk hbad
      omega
    · have hh := MiddleWindow32.actual_small_kernel_middle_window N F c hN hc hlegal
        hm hcount (by omega)
      unfold B
      omega
  · apply StarBoundConcrete30.best_omitter_threshold_unconditional N F c hc hlegal hbad
    have hs : (Avoiders F c).card≤5*N/6 := by omega
    exact hs.trans (le_max_right _ _)

#print axioms actual_two_point_crooked_capacity
#print axioms actual_two_point_crooked_ground_capacity
#print axioms actual_crooked_large_kernel_payment
#print axioms actual_crooked_omitter_middle_window
end
end JSP233.AnchorCompletion38
