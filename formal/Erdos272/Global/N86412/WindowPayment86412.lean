module

public import Erdos272.Resources.N86412.SourcePayment86412W0
public import Erdos272.Resources.N86412.SourcePayment86412W1
public import Erdos272.Resources.N86412.SourcePayment86412W2
public import Erdos272.Resources.N86412.WindowData86412

@[expose] public section

namespace JSP233.WindowPayment86412
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 WindowData86412
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
  · have hb := SourcePayment86412W0.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 88403 := by simpa [info] using hhi
        exact hn.trans (by decide : 88403 ≤ 88403))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData86412W0.G,
      SourceData86412W0.SourceUpper, SourceData86412W0.CoeffA,
      SourceData86412W0.CoeffB, SourceData86412W0.CoeffC] using hb
  · have hb := SourcePayment86412W1.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 88403 := by simpa [info] using hhi
        exact hn.trans (by decide : 88403 ≤ 88403))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData86412W1.G,
      SourceData86412W1.SourceUpper, SourceData86412W1.CoeffA,
      SourceData86412W1.CoeffB, SourceData86412W1.CoeffC] using hb
  · have hb := SourcePayment86412W2.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 88403 := by simpa [info] using hhi
        exact hn.trans (by decide : 88403 ≤ 118532))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData86412W2.G,
      SourceData86412W2.SourceUpper, SourceData86412W2.CoeffA,
      SourceData86412W2.CoeffB, SourceData86412W2.CoeffC] using hb

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment86412
