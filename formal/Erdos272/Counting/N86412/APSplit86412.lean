module

public import Erdos272.Counting.N86412.APBalanced86412

@[expose] public section

namespace JSP233.APSplit86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Suffix (p : ℤ×ℤ) : ℤ×ℤ := (p.2, 2*p.2-p.1)

theorem prefix_suffix (p : ℤ×ℤ) : Prefix (Suffix p)=p := by
  apply Prod.ext <;> dsimp only [Prefix, Suffix] <;> ring

theorem suffix_prefix (p : ℤ×ℤ) : Suffix (Prefix p)=p := by
  apply Prod.ext <;> dsimp only [Prefix, Suffix] <;> ring

theorem split_saturation {S T : Finset ℤ} {q : ℕ} (hq : 2≤q)
    (hT : IsInitial S T) (hb : BalancedTail S.card q (S\T).card)
    (heq : (Codes S q).card=intervalMultiplicity S.card q) :
    (Codes T (q-1)).card=intervalMultiplicity T.card (q-1) ∧
      (∀ p∈OrderedPairs (S\T), p∈Codes S q) ∧
      (∀ p∈Codes T (q-1), Suffix p∈Codes S q) := by
  let L := (Codes S q).filter (fun p => p.1∈T)
  let H := (Codes S q).filter (fun p => p.1∉T)
  have hq1 : 1≤q := by omega
  have hqm : 1≤q-1 := by omega
  have hqeq : q-1+1=q := Nat.sub_add_cancel hq1
  have hlo : L.card≤(Codes T (q-1)).card := by
    simpa only [L, hqeq] using low_count_le_prefix hqm hT
  have hhi : H⊆OrderedPairs (S\T) := high_subset_pairs hT
  have hhiCard : H.card≤(S\T).card.choose 2 := by
    have hh := Finset.card_le_card hhi
    simpa only [orderedPairs_card] using hh
  have hprefix := actual_AP_count_le_interval hqm T
  have hcost := balanced_split_cost hq hb
  have hcard : S.card-(S\T).card=T.card := by
    have hh := Finset.card_sdiff_add_card_eq_card hT.1
    omega
  rw [hcard] at hcost
  have hpart := Finset.card_filter_add_card_filter_not (s := Codes S q) (fun p => p.1∈T)
  change L.card+H.card=(Codes S q).card at hpart
  have hLCard : L.card=(Codes T (q-1)).card := by omega
  have hHCard : H.card=(S\T).card.choose 2 := by omega
  have hoptimal : (Codes T (q-1)).card=intervalMultiplicity T.card (q-1) := by omega
  have hhighEq : H=OrderedPairs (S\T) := by
    apply Finset.eq_of_subset_of_card_le hhi
    exact le_of_eq ((orderedPairs_card (S\T)).trans hHCard.symm)
  have hmap : L.image Prefix⊆Codes T (q-1) := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hr, hrT⟩ := Finset.mem_filter.mp hr
    exact prefix_mem_of_penultimate hqm hT (by simpa only [hqeq] using hr) hrT
  have himageCard : (L.image Prefix).card=(Codes T (q-1)).card := by
    rw [Finset.card_image_of_injective L prefix_injective]
    exact hLCard
  have himage : L.image Prefix=Codes T (q-1) := by
    apply Finset.eq_of_subset_of_card_le hmap
    exact le_of_eq himageCard.symm
  refine ⟨hoptimal, ?_, ?_⟩
  · intro p hp
    have hpH : p∈H := by rw [hhighEq]; exact hp
    exact (Finset.mem_filter.mp hpH).1
  · intro p hp
    have hpI : p∈L.image Prefix := by rw [himage]; exact hp
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hpI
    have hrC : r∈Codes S q := (Finset.mem_filter.mp hr).1
    have hs : Suffix p=r := by rw [←he, suffix_prefix]
    rwa [hs]

#print axioms prefix_suffix
#print axioms suffix_prefix
#print axioms split_saturation
end
end JSP233.APSplit86412
