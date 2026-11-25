module

public import Erdos272.Counting.N86412.StrictAP86412
public import Erdos272.Counting.N109474.RunCount109474

@[expose] public section

namespace JSP233.StrictRunCount86412
open StarCompletion SourceBridge208 IntrinsicTriples208 ActualAPCount208
open TripleCodes208 PureSource208 APInterval208 APInteger109474
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def multiplicity (s q : ℕ) : ℕ := intervalMultiplicity s q - if 3 ≤ q then 1 else 0

def CountBound (s a h q : ℕ) : ℕ :=
  if q < h then multiplicity s q else
    min (multiplicity s q)
      ((a-q)*(multiplicity s h/(a-h))+(multiplicity s h%(a-h)-(q-h)))

def Price (s e h : ℕ) : ℕ :=
  s.choose 3 - ∑ q ∈ Finset.Ico 2 (s-e), Nat.totient q*CountBound s (s-e) h q

theorem actual_base_bound {S : Finset ℤ} {e q : ℕ}
    (he₂ : 2 ≤ e) (he : e ≤ Defect S) (hq : 1 ≤ q) :
    (Codes S q).card ≤ multiplicity S.card q := by
  have hh := StrictAP86412.actual_count_le (by omega : 1 ≤ e) he hq
  simpa [multiplicity, StrictAP86412.CountBound, StrictAP86412.Eps, he₂] using hh

theorem actual_count_bound {S : Finset ℤ} {e h q : ℕ}
    (he₂ : 2 ≤ e) (he : e ≤ Defect S)
    (hh : 1 ≤ h) (hha : h < S.card-e) (hq : 2 ≤ q) (hqa : q < S.card-e)
    (hmax : MaxAPSize S ≤ S.card-e) :
    (Codes S q).card ≤ CountBound S.card (S.card-e) h q := by
  have hI := actual_base_bound he₂ he (by omega : 1 ≤ q)
  unfold CountBound
  split_ifs with hqh
  · exact hI
  · apply le_min hI
    apply count_integer_bound hh (by omega : h ≤ q) hqa hmax
    exact actual_base_bound he₂ he hh

theorem actual_run_source {S : Finset ℤ} {e h : ℕ}
    (hS : 2 ≤ S.card) (he₂ : 2 ≤ e) (he : e ≤ Defect S)
    (hh : 1 ≤ h) (hha : h < S.card-e) : Price S.card e h ≤ (Pool S).card := by
  have hmax : MaxAPSize S ≤ S.card-e := by
    have hcard := maxAPSize_le_card S
    unfold Defect at he
    omega
  have hb := RunCount118533.actual_intrinsic_of_counts (CountBound S.card (S.card-e) h) hmax (by
    intro q hq
    obtain ⟨hq₂, hqa⟩ := Finset.mem_Ico.mp hq
    exact actual_count_bound he₂ he hh hha hq₂ hqa hmax)
  unfold Price
  omega

#print axioms actual_base_bound
#print axioms actual_count_bound
#print axioms actual_run_source
end
end JSP233.StrictRunCount86412
