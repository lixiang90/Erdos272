module

public import Erdos272.Resources.N200000.SourcePayment200000W0
public import Erdos272.Resources.N200000.SourcePayment200000W1
public import Erdos272.Resources.N200000.SourcePayment200000W2
public import Erdos272.Resources.N200000.WindowData200000

@[expose] public section
namespace JSP233.WindowPayment200000
open StarCompletion APGeometry SevenFamily208 WindowData200000
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
  · have hl : 200000 ≤ N := by simpa [info] using hlo
    have hh : N ≤ 210000 := by simpa [info] using hhi
    have hs := SourcePayment200000W0.actual_source hl hh hlegal hbad (by simpa [info] using hsize) hsparse hAF
    have hm := SourceData200000W0.upper_mono hh
    change _ ≤ 6*SourceData200000W0.G*_+SourceData200000W0.SourceUpper 210000
    linarith only [hs, hm]
  · have hl : 210001 ≤ N := by simpa [info] using hlo
    have hh : N ≤ 220000 := by simpa [info] using hhi
    have hs := SourcePayment200000W1.actual_source hl hh hlegal hbad (by simpa [info] using hsize) hsparse hAF
    have hm := SourceData200000W1.upper_mono hh
    change _ ≤ 6*SourceData200000W1.G*_+SourceData200000W1.SourceUpper 220000
    linarith only [hs, hm]
  · have hl : 220001 ≤ N := by simpa [info] using hlo
    have hh : N ≤ 233810 := by simpa [info] using hhi
    have hs := SourcePayment200000W2.actual_source hl hh hlegal hbad (by simpa [info] using hsize) hsparse hAF
    have hm := SourceData200000W2.upper_mono hh
    change _ ≤ 6*SourceData200000W2.G*_+SourceData200000W2.SourceUpper 233810
    linarith only [hs, hm]
#print axioms actual_source_for_proof
end
end JSP233.WindowPayment200000
