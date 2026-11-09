module

public import Erdos272.Core.N200000.PrimePairResidue200000

@[expose] public section

/-! A first-order pair sieve on one actual interval complement. This
already gives a pure arithmetic lower source, uniform in point position. -/
namespace JSP233.PairUnionSieve200000
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open IndexedCorePairs200000 ActualCorePairs200000 PrimePairEvents200000 PrimePairResidue200000 PairEventCount200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def FirstBound (a h b : ℕ) : ℕ := a.choose 2 - b.choose 2 -
  ∑ q ∈ Primes a h, (((a + q - 1) / q).choose 2 - (b / q).choose 2)

theorem good_index_eq_space_filter (a h : ℕ) (ell : ℤ) (J : Finset ℕ) :
    GoodIndex a h ell J = (Space (Finset.range a) J).filter (Primitive h ell) := by
  ext Q
  constructor
  · intro hQ
    obtain ⟨hsub, hcard, hnot, hprim⟩ := good_index_data hQ
    refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, ?_⟩, hprim⟩
    intro hQJ
    exact hnot (Finset.mem_powersetCard.mp hQJ).1
  · intro hQ
    obtain ⟨hspace, hprim⟩ := Finset.mem_filter.mp hQ
    obtain ⟨hQA, hnotJ⟩ := Finset.mem_sdiff.mp hspace
    have hcard := (Finset.mem_powersetCard.mp hQA).2
    refine Finset.mem_filter.mpr ⟨hQA, ?_, hprim⟩
    intro hsubJ
    exact hnotJ (Finset.mem_powersetCard.mpr ⟨hsubJ, hcard⟩)

theorem space_cover {a h : ℕ} {ell : ℤ} (hc : Int.gcd (h : ℤ) ell = 1) (J : Finset ℕ) :
    Space (Finset.range a) J ⊆ GoodIndex a h ell J ∪
      (Primes a h).biUnion (BadEvent (Finset.range a) J h ell) := by
  intro Q hQ
  by_cases hprim : Primitive h ell Q
  · apply Finset.mem_union_left
    rw [good_index_eq_space_filter]
    exact Finset.mem_filter.mpr ⟨hQ, hprim⟩
  · have hpow := (Finset.mem_sdiff.mp hQ).1
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hpow
    obtain ⟨q, hq, hbad⟩ := not_primitive_has_bad hc hsub hcard hprim
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_filter.mpr ⟨hQ, hbad⟩⟩)

theorem first_order_sieve {a b l h : ℕ} {ell : ℤ} (hlen : l + b ≤ a) (hc : Int.gcd (h : ℤ) ell = 1) :
    FirstBound a h b ≤ (GoodIndex a h ell (Finset.Ico l (l + b))).card := by
  let J := Finset.Ico l (l + b)
  have hJ : J ⊆ Finset.range a := by
    intro i hi
    have hu := (Finset.mem_Ico.mp hi).2
    exact Finset.mem_range.mpr (by omega)
  have hspace : (Space (Finset.range a) J).card = a.choose 2 - b.choose 2 := by
    simpa only [J, Finset.card_range, Nat.card_Ico, Nat.add_sub_cancel_left] using space_card hJ
  have hcover : (Space (Finset.range a) J).card ≤ (GoodIndex a h ell J).card +
      ∑ q ∈ Primes a h, (BadEvent (Finset.range a) J h ell q).card := by
    apply ((Finset.card_le_card (space_cover (a := a) hc J)).trans (Finset.card_union_le _ _)).trans
    exact Nat.add_le_add_left Finset.card_biUnion_le _
  have hbad : (∑ q ∈ Primes a h, (BadEvent (Finset.range a) J h ell q).card) ≤
      ∑ q ∈ Primes a h, (((a + q - 1) / q).choose 2 - (b / q).choose 2) := by
    apply Finset.sum_le_sum
    intro q hq
    obtain ⟨_hqa, hp, hn⟩ := Finset.mem_filter.mp hq
    exact (bad_event_interval_bounds hlen hp hn ell).2
  change FirstBound a h b ≤ (GoodIndex a h ell J).card
  unfold FirstBound
  omega

theorem actual_source_of_first_bound {S : Finset ℤ} {U : ℕ} (hS : 2 ≤ S.card)
    (hc : ∀ h : ℕ, 0 < h → U ≤ FirstBound (MaxAPSize S) h (ExceptionLength (MaxAPSize S) h)) :
    Defect S * U ≤ (Pool S).card := by
  apply actual_defect_source_of_index_bound hS
  intro h hh ell hcop l hlen
  exact (hc h hh).trans (first_order_sieve hlen hcop)

#print axioms good_index_eq_space_filter
#print axioms space_cover
#print axioms first_order_sieve
#print axioms actual_source_of_first_bound
end
end JSP233.PairUnionSieve200000
