module

public import Erdos272.Resources.N82427.SourceAmbient82427
public import Erdos272.Resources.N82427.SourcePayment82427W0
public import Erdos272.Resources.N82427.SourcePayment82427W1
public import Erdos272.Resources.N82427.SourcePayment82427W2
public import Erdos272.Resources.N82427.WindowData82427

@[expose] public section

namespace JSP233.WindowPayment82427
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 WindowData82427
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem actual_source_for_proof {w N : ℕ} {A F : Finset (Finset ℤ)}
    (hw : w < 4) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ F, ((Pool S).card : ℝ))+Fee w N := by
  interval_cases w
  · have hb := SourcePayment82427W0.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData82427W0.G,
      SourceData82427W0.SourceUpper,SourceData82427W0.CoeffA,
      SourceData82427W0.CoeffB,SourceData82427W0.CoeffC] using hb
  · have hb := SourcePayment82427W1.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData82427W1.G,
      SourceData82427W1.SourceUpper,SourceData82427W1.CoeffA,
      SourceData82427W1.CoeffB,SourceData82427W1.CoeffC] using hb
  · have hb := SourcePayment82427W2.actual_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hAF
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData82427W2.G,
      SourceData82427W2.SourceUpper,SourceData82427W2.CoeffA,
      SourceData82427W2.CoeffB,SourceData82427W2.CoeffC] using hb
  · have hn : N ≤ 86412 := by
      have hh : N ≤ 84363 := by simpa [info] using hhi
      omega
    have hb := SourceAmbient82427.actual_source hn hlegal hbad
      (by simpa [info] using hsize) hsparse hAF
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceAmbient82427.Constant] using hb

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment82427
