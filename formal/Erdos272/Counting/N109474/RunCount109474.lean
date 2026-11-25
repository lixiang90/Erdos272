module

public import Erdos272.Counting.N109474.APInteger109474
public import Erdos272.Counting.N118533.RunCount118533

@[expose] public section

namespace JSP233.RunCount109474
open StarCompletion SourceBridge208 IntrinsicTriples208 ActualAPCount208
open TripleCodes208 PureSource208 APInterval208 APInteger109474
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def CountBound (s a h q : ℕ) : ℕ :=
  if q < h then intervalMultiplicity s q else
    min (intervalMultiplicity s q)
      ((a-q)*(intervalMultiplicity s h/(a-h))+(intervalMultiplicity s h%(a-h)-(q-h)))

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
  · exact le_min hI (count_integer_bound hh (by omega : h ≤ q) hqa hmax
      (actual_AP_count_le_interval hh S))

theorem actual_run_source {S : Finset ℤ} {e h : ℕ}
    (hS : 2 ≤ S.card) (he : e ≤ Defect S) (hh : 1 ≤ h) (hha : h < S.card-e) :
    Price S.card e h ≤ (Pool S).card := by
  have hcard := maxAPSize_le_card S
  have hmax : MaxAPSize S ≤ S.card-e := by unfold Defect at he; omega
  have hb := RunCount118533.actual_intrinsic_of_counts (CountBound S.card (S.card-e) h) hmax (by
    intro q hq
    obtain ⟨hq2, hqa⟩ := Finset.mem_Ico.mp hq
    exact actual_count_bound hh hha hq2 hqa hmax)
  unfold Price
  omega

#print axioms actual_count_bound
#print axioms actual_run_source
end
end JSP233.RunCount109474
