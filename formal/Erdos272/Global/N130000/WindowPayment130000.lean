module

public import Erdos272.Resources.N130000.SourcePayment130000W0
public import Erdos272.Resources.N130000.SourcePayment130000W1
public import Erdos272.Resources.N130000.SourcePayment130000W2
public import Erdos272.Resources.N130000.SourcePayment130000W3
public import Erdos272.Resources.N130000.WindowData130000

@[expose] public section

namespace JSP233.WindowPayment130000
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 WindowData130000
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
  · have hb := SourcePayment130000W0.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData130000W0.G,
      SourceData130000W0.SourceUpper, SourceData130000W0.CoeffA,
      SourceData130000W0.CoeffB, SourceData130000W0.CoeffC] using hb
  · have hb := SourcePayment130000W1.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData130000W1.G,
      SourceData130000W1.SourceUpper, SourceData130000W1.CoeffA,
      SourceData130000W1.CoeffB, SourceData130000W1.CoeffC] using hb
  · have hb := SourcePayment130000W2.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData130000W2.G,
      SourceData130000W2.SourceUpper, SourceData130000W2.CoeffA,
      SourceData130000W2.CoeffB, SourceData130000W2.CoeffC] using hb
  · have hb := SourcePayment130000W3.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G, Fee, CoeffA, CoeffB, CoeffC, SourceData130000W3.G,
      SourceData130000W3.SourceUpper, SourceData130000W3.CoeffA,
      SourceData130000W3.CoeffB, SourceData130000W3.CoeffC] using hb

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment130000
