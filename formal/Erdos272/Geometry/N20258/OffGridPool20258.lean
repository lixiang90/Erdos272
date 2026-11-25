module

public import Erdos272.Geometry.N20258.OffGridProgressions20258

@[expose] public section

/-! Covered pairs for one off-grid point form disjoint midpoint pairs.
Their number is at most half the actual core cardinality. -/
namespace JSP233.OffGridPool20258
open StarCompletion IntrinsicTriples208 PairPool200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def MidPairs (P : Finset ℤ) (x : ℤ) : Finset (Finset ℤ) :=
  (P.powersetCard 2).filter (fun Q => ∑ y ∈ Q, y = 2 * x)

def Covered (S P : Finset ℤ) (x : ℤ) : Finset (Finset ℤ) := P.powersetCard 2 \ GoodPairs S P x

theorem pair_eq_of_common_sum {Q R : Finset ℤ} {z : ℤ}
    (hQ : Q.card = 2) (hR : R.card = 2) (hs : (∑ y ∈ Q, y) = ∑ y ∈ R, y)
    (hzQ : z ∈ Q) (hzR : z ∈ R) : Q = R := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hQ
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hR
  have hsum : a + b = c + d := by simpa [hab, hcd] using hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzQ hzR
  rcases hzQ with hzQ | hzQ <;> rcases hzR with hzR | hzR
  · have hac : a = c := by omega
    have hbd : b = d := by omega
    simp only [hac, hbd]
  · have had : a = d := by omega
    have hbc : b = c := by omega
    rw [had, hbc, Finset.pair_comm]
  · have had : a = d := by omega
    have hbc : b = c := by omega
    rw [had, hbc, Finset.pair_comm]
  · have hac : a = c := by omega
    have hbd : b = d := by omega
    simp only [hac, hbd]

theorem midpoint_disjoint (P : Finset ℤ) (x : ℤ) :
    ((MidPairs P x : Finset (Finset ℤ)) : Set (Finset ℤ)).PairwiseDisjoint id := by
  intro Q hQ R hR hne
  apply Finset.disjoint_left.mpr
  intro z hzQ hzR
  obtain ⟨hQpow, hQsum⟩ := Finset.mem_filter.mp hQ
  obtain ⟨hRpow, hRsum⟩ := Finset.mem_filter.mp hR
  exact hne (pair_eq_of_common_sum (Finset.mem_powersetCard.mp hQpow).2
    (Finset.mem_powersetCard.mp hRpow).2 (hQsum.trans hRsum.symm) hzQ hzR)

theorem midpoint_card (P : Finset ℤ) (x : ℤ) : 2 * (MidPairs P x).card ≤ P.card := by
  have hsub : (MidPairs P x).biUnion id ⊆ P := by
    intro y hy
    obtain ⟨Q, hQ, hyQ⟩ := Finset.mem_biUnion.mp hy
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hQ).1).1 hyQ
  have hcard : ((MidPairs P x).biUnion id).card = 2 * (MidPairs P x).card := by
    rw [Finset.card_biUnion (midpoint_disjoint P x)]
    calc
      _ = ∑ _Q ∈ MidPairs P x, 2 := by
        apply Finset.sum_congr rfl
        intro Q hQ
        exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hQ).1).2
      _ = _ := by simp [Nat.mul_comm]
  rw [← hcard]
  exact Finset.card_le_card hsub

theorem covered_subset_midpoint {S P : Finset ℤ} {d p x : ℤ} (hPS : P ⊆ S) (hx : x ∈ S)
    (hphase : ∀ y ∈ P, d ∣ y - p) (hrest : ∀ y ∈ S, y ≠ x → d ∣ y - p)
    (hnot : ¬d ∣ x - p) : Covered S P x ⊆ MidPairs P x := by
  intro Q hQ
  obtain ⟨hQpow, hnotgood⟩ := Finset.mem_sdiff.mp hQ
  obtain ⟨hQP, hcard⟩ := Finset.mem_powersetCard.mp hQpow
  have hxP : x ∉ P := fun hh => hnot (hphase x hh)
  have hxQ : x ∉ Q := fun hh => hxP (hQP hh)
  have hnotpool : insert x Q ∉ Pool S := fun hh =>
    hnotgood (Finset.mem_filter.mpr ⟨hQpow, hh⟩)
  have hsub : insert x Q ⊆ S := Finset.insert_subset_iff.mpr ⟨hx, hQP.trans hPS⟩
  have hthree : (insert x Q).card = 3 := by rw [Finset.card_insert_of_notMem hxQ, hcard]
  have hcover : ∃ T : Finset ℤ, IsAP T ∧ insert x Q ⊆ T ∧ T ⊆ S := by
    by_contra hn
    exact hnotpool (mem_pool.mpr ⟨hsub, hthree, hn⟩)
  obtain ⟨T, hT, hQT, hTS⟩ := hcover
  obtain ⟨a, c, hac, hpair⟩ := Finset.card_eq_two.mp hcard
  have haQ : a ∈ Q := by rw [hpair]; simp
  have hcQ : c ∈ Q := by rw [hpair]; simp
  have hmid := OffGridProgressions20258.offphase_cover_midpoint hT (hQT (Finset.mem_insert_self _ _))
    (hQT (Finset.mem_insert_of_mem haQ)) (hQT (Finset.mem_insert_of_mem hcQ)) hac
    (fun y hy hyx => hrest y (hTS hy) hyx) hnot (hphase a (hQP haQ)) (hphase c (hQP hcQ))
  apply Finset.mem_filter.mpr
  refine ⟨hQpow, ?_⟩
  rw [hpair]
  simpa only [Finset.sum_pair hac] using hmid

theorem actual_pair_bound {S P : Finset ℤ} {d p x : ℤ} (hPS : P ⊆ S) (hx : x ∈ S)
    (hphase : ∀ y ∈ P, d ∣ y - p) (hrest : ∀ y ∈ S, y ≠ x → d ∣ y - p)
    (hnot : ¬d ∣ x - p) :
    P.card.choose 2 ≤ (GoodPairs S P x).card + P.card / 2 := by
  have hgood : GoodPairs S P x ⊆ P.powersetCard 2 := Finset.filter_subset _ _
  have hsum := Finset.card_sdiff_add_card_eq_card hgood
  have hcov := Finset.card_le_card (covered_subset_midpoint hPS hx hphase hrest hnot)
  have hmid := midpoint_card P x
  rw [Finset.card_powersetCard] at hsum
  change (Covered S P x).card + (GoodPairs S P x).card = P.card.choose 2 at hsum
  omega

theorem actual_pool_bound {S P : Finset ℤ} {d p x : ℤ} (hPS : P ⊆ S) (hx : x ∈ S)
    (hphase : ∀ y ∈ P, d ∣ y - p) (hrest : ∀ y ∈ S, y ≠ x → d ∣ y - p)
    (hnot : ¬d ∣ x - p) : P.card.choose 2 - P.card / 2 ≤ (Pool S).card := by
  have hxP : x ∉ P := fun hh => hnot (hphase x hh)
  have hsub : PointTriples S P x ⊆ Pool S := by
    intro T hT
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hT
    exact (good_pair_data hQ).2.2
  have hp := Finset.card_le_card hsub
  rw [point_triples_card hxP] at hp
  have hh := actual_pair_bound hPS hx hphase hrest hnot
  omega

#print axioms pair_eq_of_common_sum
#print axioms midpoint_disjoint
#print axioms midpoint_card
#print axioms covered_subset_midpoint
#print axioms actual_pair_bound
#print axioms actual_pool_bound
end
end JSP233.OffGridPool20258
