module

public import Erdos272.Resources.N142758.SourcePayment142758W0
public import Erdos272.Resources.N142758.SourcePayment142758W1
public import Erdos272.Resources.N142758.SourcePayment142758W2
public import Erdos272.Resources.N142758.WindowData142758

@[expose] public section

namespace JSP233.WindowPayment142758
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 WindowData142758
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
  · have hb := SourcePayment142758W0.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData142758W0.G,
      SourceData142758W0.SourceUpper, SourceData142758W0.CoeffA,
      SourceData142758W0.CoeffB, SourceData142758W0.CoeffC] using hb
  · have hb := SourcePayment142758W1.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData142758W1.G,
      SourceData142758W1.SourceUpper, SourceData142758W1.CoeffA,
      SourceData142758W1.CoeffB, SourceData142758W1.CoeffC] using hb
  · have hb := SourcePayment142758W2.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData142758W2.G,
      SourceData142758W2.SourceUpper, SourceData142758W2.CoeffA,
      SourceData142758W2.CoeffB, SourceData142758W2.CoeffC] using hb

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment142758
