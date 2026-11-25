module

public import Erdos272.Resources.N82427.SourceAmbient82427
public import Erdos272.Resources.N80470.SourcePayment80470W0
public import Erdos272.Resources.N80470.SourcePayment80470W1
public import Erdos272.Resources.N80470.SourcePayment80470W2
public import Erdos272.Global.N80470.CommonBounds80470

@[expose] public section

namespace JSP233.WindowPayment80470
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 WindowData80470
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem actual_source_for_proof {w N : ℕ} {A F : Finset (Finset ℤ)}
    (hw : w < 4) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hlegalF : Legal (Ground N) F)
    (hAF : A ⊆ F) (hwitness : CommonBounds80470.WitnessCondition w F) :
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ A, ((Pool S).card : ℝ))+Fee w N := by
  interval_cases w
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment80470W0.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData80470W0.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData80470W0.G,
      SourceData80470W0.SourceUpper,SourceData80470W0.CoeffA,
      SourceData80470W0.CoeffB,SourceData80470W0.CoeffC] using hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment80470W1.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData80470W1.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData80470W1.G,
      SourceData80470W1.SourceUpper,SourceData80470W1.CoeffA,
      SourceData80470W1.CoeffB,SourceData80470W1.CoeffC] using hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment80470W2.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData80470W2.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData80470W2.G,
      SourceData80470W2.SourceUpper,SourceData80470W2.CoeffA,
      SourceData80470W2.CoeffB,SourceData80470W2.CoeffC] using hb
  · have hn : N ≤ 86412 := by
      have hh : N ≤ 82425 := by simpa [info] using hhi
      omega
    have hb := SourceAmbient82427.actual_source hn hlegal hbad
      (by simpa [info] using hsize) hsparse (le_refl A)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceAmbient82427.Constant] using hb

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment80470
