module

public import Erdos272.Resources.N158375.SourcePayment158375W0
public import Erdos272.Resources.N158375.SourcePayment158375W1
public import Erdos272.Resources.N158375.SourcePayment158375W2
public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowPayment158375
open StarCompletion APGeometry WindowData158375 IntrinsicTriples208 SourceBridge208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_source_for_proof {N w : ℕ} {A F : Finset (Finset ℤ)}
    (hw : w < 3) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ F, ((Pool S).card : ℝ))+Fee w N := by
  interval_cases w
  · have hb := SourcePayment158375W0.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData158375W0.G,
      SourceData158375W0.SourceUpper, SourceData158375W0.CoeffA,
      SourceData158375W0.CoeffB, SourceData158375W0.CoeffC,
      ] using hb
  · have hb := SourcePayment158375W1.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData158375W1.G,
      SourceData158375W1.SourceUpper, SourceData158375W1.CoeffA,
      SourceData158375W1.CoeffB, SourceData158375W1.CoeffC,
      ] using hb
  · have hb := SourcePayment158375W2.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData158375W2.G,
      SourceData158375W2.SourceUpper, SourceData158375W2.CoeffA,
      SourceData158375W2.CoeffB, SourceData158375W2.CoeffC,
      ] using hb

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment158375
