module

public import Erdos272.Resources.N118533.SourcePayment118533W0
public import Erdos272.Resources.N118533.SourcePayment118533W1
public import Erdos272.Resources.N118533.SourcePayment118533W2
public import Erdos272.Resources.N118533.WindowData118533

@[expose] public section

namespace JSP233.WindowPayment118533
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 WindowData118533
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
  · have hb := SourcePayment118533W0.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 125563 := by simpa [info] using hhi
        exact hn.trans (by decide : 125563 ≤ 125563))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData118533W0.G,
      SourceData118533W0.SourceUpper, SourceData118533W0.CoeffA,
      SourceData118533W0.CoeffB, SourceData118533W0.CoeffC] using hb
  · have hb := SourcePayment118533W1.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 129999 := by simpa [info] using hhi
        exact hn.trans (by decide : 129999 ≤ 132797))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData118533W1.G,
      SourceData118533W1.SourceUpper, SourceData118533W1.CoeffA,
      SourceData118533W1.CoeffB, SourceData118533W1.CoeffC] using hb
  · have hb := SourcePayment118533W2.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 129999 := by simpa [info] using hhi
        exact hn.trans (by decide : 129999 ≤ 179999))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData118533W2.G,
      SourceData118533W2.SourceUpper, SourceData118533W2.CoeffA,
      SourceData118533W2.CoeffB, SourceData118533W2.CoeffC] using hb

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment118533
