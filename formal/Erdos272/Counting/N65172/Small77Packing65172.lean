module

public import Erdos272.Core.N65172.Small77Kernel65172
public import Mathlib.Data.Finset.Powerset

@[expose] public section

namespace JSP233.Small77Packing65172
open StarCompletion Small77Kernel65172
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pair_packing {N : ℕ} {H : Finset (Finset ℤ)}
    (hground : ∀S∈H,S⊆Ground N) (hcard : ∀S∈H,S.card=77)
    (hinter : ∀S∈H,∀T∈H,S≠T→(S∩T).card≤1) :
    H.card≤N*(N-1)/5852 := by
  have hd : (H : Set (Finset ℤ)).PairwiseDisjoint (fun S=>S.powersetCard 2) := by
    intro S hS T hT hne
    apply Finset.disjoint_left.mpr
    intro Q hQS hQT
    obtain ⟨hsubS,hc⟩ := Finset.mem_powersetCard.mp hQS
    obtain ⟨hsubT,_hc⟩ := Finset.mem_powersetCard.mp hQT
    have hb := (Finset.card_le_card (Finset.subset_inter hsubS hsubT)).trans (hinter S hS T hT hne)
    omega
  have hsub : H.biUnion (fun S=>S.powersetCard 2)⊆(Ground N).powersetCard 2 := by
    intro Q hQ
    obtain ⟨S,hS,hQS⟩ := Finset.mem_biUnion.mp hQ
    obtain ⟨hQS,hc⟩ := Finset.mem_powersetCard.mp hQS
    exact Finset.mem_powersetCard.mpr ⟨hQS.trans (hground S hS),hc⟩
  have hb := Finset.card_le_card hsub
  rw [Finset.card_biUnion hd,Finset.card_powersetCard,ground_card] at hb
  have he : (∑S∈H,(S.powersetCard 2).card)=H.card*2926 := by
    simp only [Finset.card_powersetCard]
    have hh : ∀S∈H,S.card.choose 2=2926 := by
      intro S hS
      rw [hcard S hS]
      norm_num [Nat.choose_two_right]
    rw [Finset.sum_congr rfl hh]
    simp
  rw [he] at hb
  have hc := Nat.div_mul_le_self (N*(N-1)) 2
  rw [←Nat.choose_two_right] at hc
  apply (Nat.le_div_iff_mul_le (by decide : 0<5852)).mpr
  calc
    H.card*5852 = (H.card*2926)*2 := by ring
    _ ≤ (N.choose 2)*2 := Nat.mul_le_mul_right 2 hb
    _ ≤ N*(N-1) := hc

theorem thin_of_no_witnesses {N : ℕ} {H : Finset (Finset ℤ)}
    (hN : 677≤N) (hlegal : Legal (Ground N) H)
    (hbad : ∀S∈H,¬IsAP S) (hcard : ∀S∈H,S.card=77)
    (hkernel : PrivateFinset.Kernel (Ground N) H=∅)
    (hlarge : ∀ A∈H,∀ B∈H,A≠B→2≤(A∩B).card→(A∩B).card=76)
    (hnoone : ∀ A∈H,∀ B∈H,A≠B→(A∩B).card=76→∀T∈H,(T∩(A∩B)).card≠1) :
    H.card≤N*(N-1)/5852 := by
  by_cases hex : ∃A∈H,∃B∈H,A≠B ∧ (A∩B).card=76
  · obtain ⟨A,hA,B,hB,hne,hAB⟩ := hex
    have hc := fixed_core_card hlegal hbad hcard hkernel hlarge hnoone hA hB hne hAB
    have hn : 676≤N-1 := by omega
    have hp := Nat.mul_le_mul hN hn
    apply (Nat.le_div_iff_mul_le (by decide : 0<5852)).mpr
    have hsmall := Nat.mul_le_mul_right 5852 hc
    have hnum : (78 : ℕ)*5852≤677*676 := by norm_num
    exact hsmall.trans (hnum.trans hp)
  · apply pair_packing hlegal.1 hcard
    intro S hS T hT hne
    by_contra hn
    exact hex ⟨S,hS,T,hT,hne,hlarge S hS T hT hne (by omega)⟩

#print axioms pair_packing
#print axioms thin_of_no_witnesses
end
end JSP233.Small77Packing65172
