module

public import Erdos272.Foundation.ChainGeometry
public import Erdos272.Foundation.PeelingCapacity
public import Erdos272.Foundation.APGeometry

@[expose] public section

namespace JSP233.ChainCapacity

open StarCompletion PrivateFinset ChainGeometry

/-- Genuine chain geometry supplies the hereditary point-existence input.
No private point or cardinal budget is an assumption of this theorem. -/
theorem chain_hereditary_private (D : Finset (Finset Int)) (A : Finset Int)
    (hk : 2 ≤ A.card) (hcore : ∀ S ∈ D, A ⊆ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (hchain : PairStepChain D) : PeelingCapacity.HereditaryPrivate D := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  intro E hED htwo
  have hcrookedE : ∀ S ∈ E, ¬ IsAP S := fun S hS => hcrooked S (hED hS)
  have hpairE : ∀ S ∈ E, ∀ T ∈ E, S ≠ T → IsAP (S ∩ T) :=
    fun S hS T hT hne => hpair S (hED hS) T (hED hT) hne
  have haE : ∀ S ∈ E, a ∈ S := fun S hS => hcore S (hED hS) ha
  have hbE : ∀ S ∈ E, b ∈ S := fun S hS => hcore S (hED hS) hb
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact chain_private_exists E a b htwo hlt haE hbE hcrookedE hpairE (hchain.mono hED)
  · exact chain_private_exists E b a htwo hlt hbE haE hcrookedE hpairE (hchain.mono hED)

/-- The fixed-anchor version persists under deletion, including a final
single crooked member. The physical ground is never compressed. -/
theorem fixed_anchor_card_bound
    (Ω A : Finset Int) (D : Finset (Finset Int))
    (hD : D.Nonempty) (hA : IsAP A) (hk : 2 ≤ A.card)
    (hground : ∀ S ∈ D, S ⊆ Ω) (hcore : ∀ S ∈ D, A ⊆ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (hchain : PairStepChain D) : D.card + A.card ≤ Ω.card := by
  obtain ⟨S,hS⟩ := hD
  exact PeelingCapacity.hereditary_private_card_bound Ω A D hA
    ((hcore S hS).trans (hground S hS)) hground hcore hcrooked
    (chain_hereditary_private D A hk hcore hcrooked hpair hchain)

/-- Actual common-kernel capacity, independent of the starred extremum. -/
theorem actual_kernel_card_bound (Ω : Finset Int) (D : Finset (Finset Int))
    (hm : 2 ≤ D.card) (hk : 2 ≤ (Kernel Ω D).card)
    (hground : ∀ S ∈ D, S ⊆ Ω) (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (hchain : PairStepChain D) : D.card + (Kernel Ω D).card ≤ Ω.card := by
  have hKne : (Kernel Ω D).Nonempty := Finset.card_pos.mp (by omega)
  have hKAP : IsAP (Kernel Ω D) :=
    APGeometry.actual_common_kernel_isAP Ω D hground hpair hm hKne
  apply fixed_anchor_card_bound Ω (Kernel Ω D) D
    (Finset.card_pos.mp (by omega)) hKAP hk hground _ hcrooked hpair hchain
  intro S hS x hx
  exact (Finset.mem_filter.mp hx).2 S hS

theorem avoiding_root_card_bound
    (Ω : Finset Int) (D : Finset (Finset Int)) (c : Int)
    (hc : c ∈ Ω) (hm : 2 ≤ D.card) (hk : 2 ≤ (Kernel Ω D).card)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (hchain : PairStepChain D) : D.card + (Kernel Ω D).card + 1 ≤ Ω.card := by
  classical
  have hD : D.Nonempty := Finset.card_pos.mp (by omega)
  have hkernel := kernel_erase_root Ω D c hD havoid
  have hground' : ∀ S ∈ D, S ⊆ Ω.erase c := by
    intro S hS x hx
    exact Finset.mem_erase.mpr
      ⟨by intro he; exact havoid S hS (he ▸ hx),hground S hS hx⟩
  have hcap := actual_kernel_card_bound (Ω.erase c) D hm (by simpa [hkernel] using hk)
    hground' hcrooked hpair hchain
  rw [hkernel,Finset.card_erase_of_mem hc] at hcap
  have hΩpos := Finset.card_pos.mpr ⟨c,hc⟩
  omega

theorem chain_avoiders_payment
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (B : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hm : 2 ≤ (Avoiders F c).card) (hk : 2 ≤ (CommonKernel Ω F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hchain : PairStepChain (Avoiders F c)) : F.card + 1 ≤ B := by
  have hcap := avoiding_root_card_bound Ω (Avoiders F c) c hc hm hk
    (fun S hS => hF.1 S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2) hcrooked
    (fun S hS T hT hne => hF.2 S (Finset.mem_filter.mp hS).1
      T (Finset.mem_filter.mp hT).1 hne) hchain
  change (Avoiders F c).card + (CommonKernel Ω F c).card + 1 ≤ Ω.card at hcap
  have hpay := completion_payment Ω F c B hc hF hstar
  omega

#print axioms chain_hereditary_private
#print axioms fixed_anchor_card_bound
#print axioms actual_kernel_card_bound
#print axioms avoiding_root_card_bound
#print axioms chain_avoiders_payment

end JSP233.ChainCapacity
