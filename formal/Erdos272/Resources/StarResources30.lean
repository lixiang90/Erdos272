module

public import Erdos272.Foundation.PrivatePairExistence
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.SDiff

@[expose] public section

/-! Actual common-root resource accounting. The AP-line estimate is a
separate geometric input here; none of the resource inequalities below
assumes StarBound or an extremal cardinality bound for the original family. -/
namespace JSP233.StarResources30
open StarCompletion PrivatePairExistence
open scoped Classical

noncomputable section
variable (c : ℤ) (Ω : Finset ℤ) (F : Finset (Finset ℤ))

def APLarge : Finset (Finset ℤ) := F.filter (fun S => IsAP S ∧ 4 ≤ S.card)
def APTriples : Finset (Finset ℤ) := F.filter (fun S => IsAP S ∧ S.card=3)
def APSmall : Finset (Finset ℤ) := F.filter (fun S => IsAP S ∧ S.card≤2)
def PairUniverse : Finset (Finset ℤ) := (Ω.erase c).powersetCard 2
def TriplePairs : Finset (Finset ℤ) := (APTriples F).image (fun S => S.erase c)
def CoveredAPBadPairs : Finset (Finset ℤ) := Ω.powerset.filter (fun Q =>
  Q.card=2 ∧ c∉Q ∧ ¬IsAP (insert c Q) ∧ ∃ S∈F, IsAP S ∧ Q⊆S)

theorem ap_partition : (APSmall F).card+(APTriples F).card+(APLarge F).card =
    (F.filter IsAP).card := by
  classical
  have h1 : Disjoint (APSmall F) (APTriples F) := by
    apply Finset.disjoint_left.mpr
    intro S hS hT
    simp only [APSmall,APTriples,Finset.mem_filter] at hS hT
    omega
  have h2 : Disjoint (APSmall F ∪ APTriples F) (APLarge F) := by
    apply Finset.disjoint_left.mpr
    intro S hS hT
    have hT := Finset.mem_filter.mp hT
    rcases Finset.mem_union.mp hS with hS | hS
    · have hS := Finset.mem_filter.mp hS
      omega
    · have hS := Finset.mem_filter.mp hS
      omega
  have he : APSmall F ∪ APTriples F ∪ APLarge F = F.filter IsAP := by
    ext S
    simp only [APSmall,APTriples,APLarge,Finset.mem_union,Finset.mem_filter]
    constructor
    · aesop
    · rintro ⟨hS,hA⟩
      by_cases h2 : S.card≤2
      · exact Or.inl (Or.inl ⟨hS,hA,h2⟩)
      by_cases h3 : S.card=3
      · exact Or.inl (Or.inr ⟨hS,hA,h3⟩)
      · exact Or.inr ⟨hS,hA,by omega⟩
  rw [← he,Finset.card_union_of_disjoint h2,Finset.card_union_of_disjoint h1]

theorem family_partition : F.card = (APSmall F).card+(APTriples F).card+
    (APLarge F).card+(CrookedMembers F).card := by
  rw [ap_partition]
  unfold CrookedMembers
  exact (Finset.card_filter_add_card_filter_not (s:=F) IsAP).symm

theorem apSmall_subset_pairStar (hlegal : Legal Ω F) (hroot : Rooted F c) :
    APSmall F ⊆ PairStar Ω c := by
  intro S hS
  obtain ⟨hSF,hAP,hcard⟩ := Finset.mem_filter.mp hS
  have hcS := hroot S hSF
  have hSne : S.Nonempty := ⟨c,hcS⟩
  have hpos : 0<S.card := Finset.card_pos.mpr hSne
  change S∈Ω.image (fun x => ({c,x}:Finset ℤ))
  by_cases hone : S.card=1
  · obtain ⟨x,he⟩ := Finset.card_eq_one.mp hone
    have hcx : c=x := by simpa [he] using hcS
    refine Finset.mem_image.mpr ⟨x,hlegal.1 S hSF (by simp [he]),?_⟩
    simp [he,hcx]
  · have htwo : S.card=2 := by omega
    obtain ⟨x,y,hxy,he⟩ := Finset.card_eq_two.mp htwo
    have hor : c=x ∨ c=y := by simpa [he] using hcS
    rcases hor with rfl | rfl
    · refine Finset.mem_image.mpr ⟨y,hlegal.1 S hSF (by simp [he]),?_⟩
      exact he.symm
    · refine Finset.mem_image.mpr ⟨x,hlegal.1 S hSF (by simp [he]),?_⟩
      simpa [Finset.pair_comm] using he.symm

theorem apSmall_card_le (hlegal : Legal Ω F) (hroot : Rooted F c) :
    (APSmall F).card ≤ Ω.card :=
  (Finset.card_le_card (apSmall_subset_pairStar c Ω F hlegal hroot)).trans_eq
    (pairStar_card Ω c)

theorem triplePairs_card (hroot : Rooted F c) :
    (TriplePairs c F).card = (APTriples F).card := by
  classical
  apply Finset.card_image_of_injOn
  intro S hS T hT he
  change S.erase c=T.erase c at he
  have hcS := hroot S (Finset.mem_filter.mp hS).1
  have hcT := hroot T (Finset.mem_filter.mp hT).1
  calc
    S = insert c (S.erase c) := (Finset.insert_erase hcS).symm
    _ = insert c (T.erase c) := by rw [he]
    _ = T := Finset.insert_erase hcT

theorem triplePair_properties (hlegal : Legal Ω F) (hroot : Rooted F c)
    {Q : Finset ℤ} (hQ : Q∈TriplePairs c F) :
    Q∈PairUniverse c Ω ∧ IsAP (insert c Q) := by
  classical
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨hSF,hAP,hcard⟩ := Finset.mem_filter.mp hS
  have hcS := hroot S hSF
  constructor
  · apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      have hm := Finset.mem_erase.mp hx
      exact Finset.mem_erase.mpr ⟨hm.1,hlegal.1 S hSF hm.2⟩
    · rw [Finset.card_erase_of_mem hcS,hcard]
  · simpa only [Finset.insert_erase hcS] using hAP

theorem covered_subset_pairUniverse : CoveredAPBadPairs c Ω F ⊆ PairUniverse c Ω := by
  classical
  intro Q hQ
  obtain ⟨hsub,hcard,hroot,hbad,hcov⟩ := Finset.mem_filter.mp hQ
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_,hcard⟩
  intro x hx
  exact Finset.mem_erase.mpr ⟨by intro he; subst x; exact hroot hx,
    Finset.mem_powerset.mp hsub hx⟩

theorem available_subset_pairUniverse : AvailableBadPairsAt c Ω F ⊆ PairUniverse c Ω := by
  classical
  intro Q hQ
  obtain ⟨hsub,hcard,hroot,hbad,hcov⟩ := Finset.mem_filter.mp hQ
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_,hcard⟩
  intro x hx
  exact Finset.mem_erase.mpr ⟨by intro he; subst x; exact hroot hx,
    Finset.mem_powerset.mp hsub hx⟩

theorem covered_disjoint_available :
    Disjoint (CoveredAPBadPairs c Ω F) (AvailableBadPairsAt c Ω F) := by
  classical
  apply Finset.disjoint_left.mpr
  intro Q hQ hA
  obtain ⟨hpow,hcard,hroot,hbad,S,hS,hAP,hsub⟩ := Finset.mem_filter.mp hQ
  exact (Finset.mem_filter.mp hA).2.2.2.2 S hS hAP hsub

theorem triples_disjoint_covered (hlegal : Legal Ω F) (hroot : Rooted F c) :
    Disjoint (TriplePairs c F) (CoveredAPBadPairs c Ω F) := by
  classical
  apply Finset.disjoint_left.mpr
  intro Q hT hC
  exact (Finset.mem_filter.mp hC).2.2.2.1 (triplePair_properties c Ω F hlegal hroot hT).2

theorem triples_disjoint_available (hlegal : Legal Ω F) (hroot : Rooted F c) :
    Disjoint (TriplePairs c F) (AvailableBadPairsAt c Ω F) := by
  classical
  apply Finset.disjoint_left.mpr
  intro Q hT hA
  exact (Finset.mem_filter.mp hA).2.2.2.1 (triplePair_properties c Ω F hlegal hroot hT).2

theorem three_resource_pools_card_le (hlegal : Legal Ω F) (hroot : Rooted F c) :
    (APTriples F).card+(CoveredAPBadPairs c Ω F).card+(AvailableBadPairsAt c Ω F).card ≤
      (PairUniverse c Ω).card := by
  classical
  rw [← triplePairs_card c F hroot]
  have hd1 := triples_disjoint_covered c Ω F hlegal hroot
  have hd2 : Disjoint (TriplePairs c F ∪ CoveredAPBadPairs c Ω F)
      (AvailableBadPairsAt c Ω F) := Finset.disjoint_union_left.mpr
    ⟨triples_disjoint_available c Ω F hlegal hroot,covered_disjoint_available c Ω F⟩
  rw [← Finset.card_union_of_disjoint hd1,← Finset.card_union_of_disjoint hd2]
  apply Finset.card_le_card
  apply Finset.union_subset
  · exact Finset.union_subset (fun Q hQ => (triplePair_properties c Ω F hlegal hroot hQ).1)
      (covered_subset_pairUniverse c Ω F)
  · exact available_subset_pairUniverse c Ω F

theorem rooted_card_le_of_APLarge (hlegal : Legal Ω F) (hroot : Rooted F c)
    (a : ℕ) (hAP : (APLarge F).card≤(CoveredAPBadPairs c Ω F).card+a) :
    F.card ≤ Ω.card+(Ω.card-1).choose 2+a := by
  by_cases hcm : c∈Ω
  swap
  · have hF : F=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      exact hcm (hlegal.1 S hS (hroot S hS))
    simp [hF]
  have hp := three_resource_pools_card_le c Ω F hlegal hroot
  have hc := crooked_members_card_le_available_pairs_at_root hlegal hroot
  have hs := apSmall_card_le c Ω F hlegal hroot
  have hpart := family_partition F
  have hu : (PairUniverse c Ω).card = (Ω.card-1).choose 2 := by
    unfold PairUniverse
    rw [Finset.card_powersetCard,Finset.card_erase_of_mem hcm]
  omega

#print axioms ap_partition
#print axioms family_partition
#print axioms apSmall_subset_pairStar
#print axioms apSmall_card_le
#print axioms triplePairs_card
#print axioms triplePair_properties
#print axioms covered_subset_pairUniverse
#print axioms available_subset_pairUniverse
#print axioms covered_disjoint_available
#print axioms triples_disjoint_covered
#print axioms triples_disjoint_available
#print axioms three_resource_pools_card_le
#print axioms rooted_card_le_of_APLarge

end
end JSP233.StarResources30
