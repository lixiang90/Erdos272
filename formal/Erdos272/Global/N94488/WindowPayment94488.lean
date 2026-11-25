module

public import Erdos272.Resources.N94488.SourcePayment94488W0
public import Erdos272.Resources.N94488.SourcePayment94488W1
public import Erdos272.Resources.N94488.SourcePayment94488W2
public import Erdos272.Resources.N94488.SourcePayment94488W3
public import Erdos272.Resources.N94488.SourcePayment94488W4
public import Erdos272.Resources.N94488.SourcePayment94488W5
public import Erdos272.Resources.N94488.WindowData94488

@[expose] public section

namespace JSP233.WindowPayment94488
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 WindowData94488
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_source_for_proof {w N : ℕ} {A F : Finset (Finset ℤ)}
    (hw : w < 6) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ F, ((Pool S).card : ℝ))+Fee w N := by
  interval_cases w
  · have hb := SourcePayment94488W0.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 96560 := by simpa [info] using hhi
        exact hn.trans (by decide : 96560 ≤ 96560))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData94488W0.G,
      SourceData94488W0.SourceUpper, SourceData94488W0.CoeffA,
      SourceData94488W0.CoeffB, SourceData94488W0.CoeffC] using hb
  · have hb := SourcePayment94488W1.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 98656 := by simpa [info] using hhi
        exact hn.trans (by decide : 98656 ≤ 98656))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData94488W1.G,
      SourceData94488W1.SourceUpper, SourceData94488W1.CoeffA,
      SourceData94488W1.CoeffB, SourceData94488W1.CoeffC] using hb
  · have hb := SourcePayment94488W2.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 100774 := by simpa [info] using hhi
        exact hn.trans (by decide : 100774 ≤ 100774))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData94488W2.G,
      SourceData94488W2.SourceUpper, SourceData94488W2.CoeffA,
      SourceData94488W2.CoeffB, SourceData94488W2.CoeffC] using hb
  · have hb := SourcePayment94488W3.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 105079 := by simpa [info] using hhi
        exact hn.trans (by decide : 105079 ≤ 105079))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData94488W3.G,
      SourceData94488W3.SourceUpper, SourceData94488W3.CoeffA,
      SourceData94488W3.CoeffB, SourceData94488W3.CoeffC] using hb
  · have hb := SourcePayment94488W4.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 109473 := by simpa [info] using hhi
        exact hn.trans (by decide : 109473 ≤ 109473))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData94488W4.G,
      SourceData94488W4.SourceUpper, SourceData94488W4.CoeffA,
      SourceData94488W4.CoeffB, SourceData94488W4.CoeffC] using hb
  · have hb := SourcePayment94488W5.actual_source
      (by simpa [info] using hlo)
      (by
        have hn : N ≤ 109473 := by simpa [info] using hhi
        exact hn.trans (by decide : 109473 ≤ 118532))
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData94488W5.G,
      SourceData94488W5.SourceUpper, SourceData94488W5.CoeffA,
      SourceData94488W5.CoeffB, SourceData94488W5.CoeffC] using hb

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment94488
