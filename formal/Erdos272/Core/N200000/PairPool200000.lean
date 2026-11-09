module

public import Erdos272.Core.N200000.CorePairHull200000

@[expose] public section

/-! Pair sources at different actual outside points are disjoint parts
of the one intrinsic pool. A counted triple has exactly one outside point. -/
namespace JSP233.PairPool200000
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def GoodPairs (S P : Finset ℤ) (x : ℤ) : Finset (Finset ℤ) :=
  (P.powersetCard 2).filter (fun Q => insert x Q ∈ Pool S)

def PointTriples (S P : Finset ℤ) (x : ℤ) : Finset (Finset ℤ) := (GoodPairs S P x).image (insert x)

theorem good_pair_data {S P Q : Finset ℤ} {x : ℤ} (hQ : Q ∈ GoodPairs S P x) :
    Q ⊆ P ∧ Q.card = 2 ∧ insert x Q ∈ Pool S := by
  obtain ⟨hpow, hpool⟩ := Finset.mem_filter.mp hQ
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hpow
  exact ⟨hsub, hcard, hpool⟩

theorem point_triples_card {S P : Finset ℤ} {x : ℤ} (hx : x ∉ P) :
    (PointTriples S P x).card = (GoodPairs S P x).card := by
  apply Finset.card_image_of_injOn
  intro Q hQ R hR he
  have hxQ : x ∉ Q := fun hh => hx ((good_pair_data hQ).1 hh)
  have hxR : x ∉ R := fun hh => hx ((good_pair_data hR).1 hh)
  have herase := congrArg (fun T : Finset ℤ => T.erase x) he
  simpa only [Finset.erase_insert hxQ, Finset.erase_insert hxR] using herase

theorem point_triples_disjoint (S P : Finset ℤ) :
    ((S \ P : Finset ℤ) : Set ℤ).PairwiseDisjoint (PointTriples S P) := by
  intro x hx y _hy hne
  apply Finset.disjoint_left.mpr
  intro T hxT hyT
  obtain ⟨Q, _hQ, hQeq⟩ := Finset.mem_image.mp hxT
  obtain ⟨R, hR, hReq⟩ := Finset.mem_image.mp hyT
  have hxIn : x ∈ T := hQeq ▸ Finset.mem_insert_self _ _
  rw [← hReq] at hxIn
  rcases Finset.mem_insert.mp hxIn with he | hxR
  · exact hne he
  · exact (Finset.mem_sdiff.mp hx).2 ((good_pair_data hR).1 hxR)

theorem point_union_subset (S P : Finset ℤ) : (S \ P).biUnion (PointTriples S P) ⊆ Pool S := by
  intro T hT
  obtain ⟨x, _hx, hxT⟩ := Finset.mem_biUnion.mp hT
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hxT
  exact (good_pair_data hQ).2.2

theorem actual_point_pair_source {S P : Finset ℤ} {U : ℕ}
    (hpoint : ∀ x ∈ S \ P, U ≤ (GoodPairs S P x).card) : (S \ P).card * U ≤ (Pool S).card := by
  calc
    _ = ∑ _x ∈ S \ P, U := by simp
    _ ≤ ∑ x ∈ S \ P, (GoodPairs S P x).card := Finset.sum_le_sum hpoint
    _ = ∑ x ∈ S \ P, (PointTriples S P x).card := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (point_triples_card (Finset.mem_sdiff.mp hx).2).symm
    _ = ((S \ P).biUnion (PointTriples S P)).card := (Finset.card_biUnion (point_triples_disjoint S P)).symm
    _ ≤ _ := Finset.card_le_card (point_union_subset S P)

theorem actual_defect_pair_source {S P : Finset ℤ} {U : ℕ} (hP : P ⊆ S) (hcard : P.card = MaxAPSize S)
    (hpoint : ∀ x ∈ S \ P, U ≤ (GoodPairs S P x).card) : Defect S * U ≤ (Pool S).card := by
  have hh := actual_point_pair_source hpoint
  rw [Finset.card_sdiff_of_subset hP, hcard] at hh
  exact hh

#print axioms good_pair_data
#print axioms point_triples_card
#print axioms point_triples_disjoint
#print axioms point_union_subset
#print axioms actual_point_pair_source
#print axioms actual_defect_pair_source
end
end JSP233.PairPool200000
