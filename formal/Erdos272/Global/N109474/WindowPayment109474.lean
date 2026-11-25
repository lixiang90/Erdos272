module

public import Erdos272.Resources.N109474.SourcePayment109474W0
public import Erdos272.Resources.N109474.SourcePayment109474W1
public import Erdos272.Resources.N109474.SourcePayment109474W2
public import Erdos272.Resources.N109474.SourcePayment109474W3
public import Erdos272.Resources.N109474.WindowData109474

@[expose] public section

namespace JSP233.WindowPayment109474
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 WindowData109474
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_source_for_proof {w N : ℕ} {A F : Finset (Finset ℤ)}
    (hw : w < 4) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ F, ((Pool S).card : ℝ))+Fee w N := by
  interval_cases w
  · have hb := SourcePayment109474W0.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 111704 := by simpa [info] using hhi
        exact hn.trans (by decide : 111704 ≤ 111704))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData109474W0.G,
      SourceData109474W0.SourceUpper, SourceData109474W0.CoeffA,
      SourceData109474W0.CoeffB, SourceData109474W0.CoeffC] using hb
  · have hb := SourcePayment109474W1.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 113957 := by simpa [info] using hhi
        exact hn.trans (by decide : 113957 ≤ 113957))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData109474W1.G,
      SourceData109474W1.SourceUpper, SourceData109474W1.CoeffA,
      SourceData109474W1.CoeffB, SourceData109474W1.CoeffC] using hb
  · have hb := SourcePayment109474W2.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 118532 := by simpa [info] using hhi
        exact hn.trans (by decide : 118532 ≤ 118532))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData109474W2.G,
      SourceData109474W2.SourceUpper, SourceData109474W2.CoeffA,
      SourceData109474W2.CoeffB, SourceData109474W2.CoeffC] using hb
  · have hb := SourcePayment109474W3.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 118532 := by simpa [info] using hhi
        exact hn.trans (by decide : 118532 ≤ 118532))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData109474W3.G,
      SourceData109474W3.SourceUpper, SourceData109474W3.CoeffA,
      SourceData109474W3.CoeffB, SourceData109474W3.CoeffC] using hb

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment109474
