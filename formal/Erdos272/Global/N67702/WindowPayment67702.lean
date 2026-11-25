module

public import Erdos272.Resources.N67702.SourcePayment67702W0
public import Erdos272.Resources.N67702.SourcePayment67702W1
public import Erdos272.Resources.N67702.SourcePayment67702W2
public import Erdos272.Resources.N67702.SourcePayment67702W3
public import Erdos272.Resources.N67702.SourcePayment67702W4
public import Erdos272.Resources.N67702.SourcePayment67702W5
public import Erdos272.Resources.N67702.SourcePayment67702W6
public import Erdos272.Resources.N67702.SourcePayment67702W7
public import Erdos272.Resources.N67702.SourcePayment67702W8
public import Erdos272.Resources.N67702.SourcePayment67702W9
public import Erdos272.Resources.N67702.SourcePayment67702W10
public import Erdos272.Global.N67702.CommonBounds67702

@[expose] public section

namespace JSP233.WindowPayment67702
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 WindowData67702
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem actual_source_for_proof {w N : ℕ} {A F : Finset (Finset ℤ)}
    (hw : w < 11) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hlegalF : Legal (Ground N) F)
    (hAF : A ⊆ F) (hwitness : CommonBounds67702.WitnessCondition w F) :
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ A, ((Pool S).card : ℝ))+Fee w N := by
  interval_cases w
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment67702W0.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData67702W0.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W0.G,
      SourceData67702W0.SourceUpper,SourceData67702W0.CoeffA,
      SourceData67702W0.CoeffB,SourceData67702W0.CoeffC] using hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment67702W1.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData67702W1.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W1.G,
      SourceData67702W1.SourceUpper,SourceData67702W1.CoeffA,
      SourceData67702W1.CoeffB,SourceData67702W1.CoeffC] using hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment67702W2.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData67702W2.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W2.G,
      SourceData67702W2.SourceUpper,SourceData67702W2.CoeffA,
      SourceData67702W2.CoeffB,SourceData67702W2.CoeffC] using hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment67702W3.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData67702W3.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W3.G,
      SourceData67702W3.SourceUpper,SourceData67702W3.CoeffA,
      SourceData67702W3.CoeffB,SourceData67702W3.CoeffC] using hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment67702W4.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData67702W4.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W4.G,
      SourceData67702W4.SourceUpper,SourceData67702W4.CoeffA,
      SourceData67702W4.CoeffB,SourceData67702W4.CoeffC] using hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment67702W5.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData67702W5.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W5.G,
      SourceData67702W5.SourceUpper,SourceData67702W5.CoeffA,
      SourceData67702W5.CoeffB,SourceData67702W5.CoeffC] using hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment67702W6.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData67702W6.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W6.G,
      SourceData67702W6.SourceUpper,SourceData67702W6.CoeffA,
      SourceData67702W6.CoeffB,SourceData67702W6.CoeffC] using hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment67702W7.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData67702W7.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W7.G,
      SourceData67702W7.SourceUpper,SourceData67702W7.CoeffA,
      SourceData67702W7.CoeffB,SourceData67702W7.CoeffC] using hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment67702W8.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData67702W8.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W8.G,
      SourceData67702W8.SourceUpper,SourceData67702W8.CoeffA,
      SourceData67702W8.CoeffB,SourceData67702W8.CoeffC] using hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment67702W9.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀
      (by simpa [Witness, SourceData67702W9.Witness] using hW)
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W9.G,
      SourceData67702W9.SourceUpper,SourceData67702W9.CoeffA,
      SourceData67702W9.CoeffB,SourceData67702W9.CoeffC] using hb
  · have hb := SourcePayment67702W10.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF
    simpa [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W10.G,
      SourceData67702W10.SourceUpper,SourceData67702W10.CoeffA,
      SourceData67702W10.CoeffB,SourceData67702W10.CoeffC] using hb

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment67702
