module

public import Erdos272.Counting.N118533.APCodeContraction118533

@[expose] public section

namespace JSP233.RunCount118533
open StarCompletion SourceBridge208 IntrinsicTriples208 ActualAPCount208
open TripleCodes208 PureSource208 APInterval208 APCodeContraction118533
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def CountBound (s a h q : ℕ) : ℕ :=
  if q < h then intervalMultiplicity s q else
    min (intervalMultiplicity s q) ((a-q)*intervalMultiplicity s h/(a-h))

def Price (s e h : ℕ) : ℕ :=
  s.choose 3-∑ q ∈ Finset.Ico 2 (s-e), Nat.totient q*CountBound s (s-e) h q

theorem actual_count_bound {S : Finset ℤ} {a h q : ℕ}
    (hh : 1 ≤ h) (hha : h < a) (hq : 2 ≤ q) (hqa : q < a)
    (hmax : MaxAPSize S ≤ a) :
    (Codes S q).card ≤ CountBound S.card a h q := by
  have hI := actual_AP_count_le_interval (by omega : 1 ≤ q) S
  unfold CountBound
  split_ifs with hqh
  · exact hI
  · apply le_min hI
    have hc := count_contraction hh (by omega : h ≤ q) hqa hmax
    have hhI := actual_AP_count_le_interval hh S
    have hs := hc.trans (Nat.mul_le_mul_left (a-q) hhI)
    apply (Nat.le_div_iff_mul_le (by omega : 0 < a-h)).mpr
    simpa only [Nat.mul_comm] using hs

theorem actual_intrinsic_of_counts {S : Finset ℤ} {a : ℕ} (f : ℕ → ℕ)
    (hmax : MaxAPSize S ≤ a)
    (hcounts : ∀ q ∈ Finset.Ico 2 a, (Codes S q).card ≤ f q) :
    S.card.choose 3 ≤ (Pool S).card+∑ q ∈ Finset.Ico 2 a, Nat.totient q*f q := by
  have hm : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ a :=
    fun R hR hRS => (AP_card_le_max hR hRS).trans hmax
  have hcover := Finset.card_le_card (covered_subset_generated hm)
  have hsum : ((Finset.Ico 2 a).biUnion (Generated S)).card ≤
      ∑ q ∈ Finset.Ico 2 a, (Generated S q).card := Finset.card_biUnion_le
  have hpoint : ∀ q ∈ Finset.Ico 2 a,
      (Generated S q).card ≤ Nat.totient q*f q := by
    intro q hq
    calc
      _ ≤ ((Codes S q).product (Indices q)).card := Finset.card_image_le
      _ = Nat.totient q*(Codes S q).card := by
        rw [Finset.product_eq_sprod, Finset.card_product, indices_card, Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left (Nat.totient q) (hcounts q hq)
  have htotal := hcover.trans (hsum.trans (Finset.sum_le_sum hpoint))
  have hp := actual_partition S
  omega

theorem actual_run_source {S : Finset ℤ} {e h : ℕ}
    (hS : 2 ≤ S.card) (he : e ≤ Defect S) (hh : 1 ≤ h) (hha : h < S.card-e) :
    Price S.card e h ≤ (Pool S).card := by
  have hcard := maxAPSize_le_card S
  have hmax : MaxAPSize S ≤ S.card-e := by unfold Defect at he; omega
  have hb := actual_intrinsic_of_counts (CountBound S.card (S.card-e) h) hmax (by
    intro q hq
    obtain ⟨hq2, hqa⟩ := Finset.mem_Ico.mp hq
    exact actual_count_bound hh hha hq2 hqa hmax)
  unfold Price
  omega

#print axioms actual_count_bound
#print axioms actual_intrinsic_of_counts
#print axioms actual_run_source
end
end JSP233.RunCount118533
