module

public import Erdos272.Resources.N180000.SourcePayment180000W0
public import Erdos272.Resources.N180000.SourcePayment180000W1
public import Erdos272.Resources.N180000.SourcePayment180000W2
public import Erdos272.Resources.N180000.WindowData180000

@[expose] public section

namespace JSP233.WindowPayment180000
open StarCompletion APGeometry SevenFamily208 WindowData180000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem actual_source_for_proof {N w : ℕ} {A F : Finset (Finset ℤ)}
    (hw : w < 3) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ F, ((IntrinsicTriples208.Pool S).card : ℝ))+Fee w := by
  interval_cases w
  · have hl : 180000 ≤ N := by simpa [info] using hlo
    have hh : N ≤ 183000 := by simpa [info] using hhi
    have hs := SourcePayment180000W0.actual_source hl hh hlegal hbad (by simpa [info] using hsize) hsparse hAF
    have hm := SourceData180000W0.upper_mono hh
    change _ ≤ 6*SourceData180000W0.G*_+SourceData180000W0.SourceUpper 183000
    linarith only [hs, hm]
  · have hl : 183001 ≤ N := by simpa [info] using hlo
    have hh : N ≤ 186000 := by simpa [info] using hhi
    have hs := SourcePayment180000W1.actual_source hl hh hlegal hbad (by simpa [info] using hsize) hsparse hAF
    have hm := SourceData180000W1.upper_mono hh
    change _ ≤ 6*SourceData180000W1.G*_+SourceData180000W1.SourceUpper 186000
    linarith only [hs, hm]
  · have hl : 186001 ≤ N := by simpa [info] using hlo
    have hh : N ≤ 189999 := by simpa [info] using hhi
    have hs := SourcePayment180000W2.actual_source hl hh hlegal hbad (by simpa [info] using hsize) hsparse hAF
    have hm := SourceData180000W2.upper_mono hh
    change _ ≤ 6*SourceData180000W2.G*_+SourceData180000W2.SourceUpper 189999
    linarith only [hs, hm]
#print axioms actual_source_for_proof
end
end JSP233.WindowPayment180000
