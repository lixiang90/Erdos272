module

public import Erdos272.Resources.N84364.SourcePayment84364W0
public import Erdos272.Resources.N84364.SourcePayment84364W1
public import Erdos272.Resources.N84364.SourcePayment84364W2
public import Erdos272.Resources.N84364.WindowData84364

@[expose] public section

namespace JSP233.WindowPayment84364
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 WindowData84364
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_source_for_proof {w N : ℕ} {A F : Finset (Finset ℤ)}
    (hw : w < 3) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ F, ((Pool S).card : ℝ))+Fee w N := by
  interval_cases w
  · have hb := SourcePayment84364W0.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 86411 := by simpa [info] using hhi
        exact hn.trans (by decide : 86411 ≤ 86411))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData84364W0.G,
      SourceData84364W0.SourceUpper, SourceData84364W0.CoeffA,
      SourceData84364W0.CoeffB, SourceData84364W0.CoeffC] using hb
  · have hb := SourcePayment84364W1.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 86411 := by simpa [info] using hhi
        exact hn.trans (by decide : 86411 ≤ 88403))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData84364W1.G,
      SourceData84364W1.SourceUpper, SourceData84364W1.CoeffA,
      SourceData84364W1.CoeffB, SourceData84364W1.CoeffC] using hb
  · have hb := SourcePayment84364W2.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 86411 := by simpa [info] using hhi
        exact hn.trans (by decide : 86411 ≤ 118532))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData84364W2.G,
      SourceData84364W2.SourceUpper, SourceData84364W2.CoeffA,
      SourceData84364W2.CoeffB, SourceData84364W2.CoeffC] using hb

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment84364
