module

public import Erdos272.Global.N65968.CommonBounds65968
public import Erdos272.Resources.N65968.SourcePayment65968W0
public import Erdos272.Resources.N65968.SourcePayment65968W1
public import Erdos272.Resources.N65968.SourcePayment65968W2
public import Erdos272.Resources.N65968.SourcePayment65968W3
public import Erdos272.Resources.N65968.SourcePayment65968W4
public import Erdos272.Resources.N65968.SourcePayment65968W5
public import Erdos272.Resources.N65968.SourcePayment65968W6
public import Erdos272.Resources.N65968.SourcePayment65968W7

@[expose] public section

namespace JSP233.WindowPayment65968
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 WindowData65968
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_source_for_proof {w N : ℕ} {A F : Finset (Finset ℤ)}
    (hw : w<8) (hlo : (info w).low≤N) (hhi : N≤(info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S∈A, ¬IsAP S)
    (hsize : ∀ S∈A, (info w).memberFloor≤S.card)
    (hsparse : ∀ S∈A, 12*S.card≤N) (hlegalF : Legal (Ground N) F)
    (hAF : A⊆F) (hwitness : CommonBounds65968.WitnessCondition w F) :
    (A.card : ℝ)≤6*G w*(∑ S∈A, ((Pool S).card : ℝ))+Fee w N := by
  interval_cases w
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment65968W0.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀ (by simpa [Witness,SourceScalars65968W0.Witness] using hW)
    norm_num [G,Fee,CoeffA,CoeffB,CoeffC,SourceScalars65968W0.G,
      SourceScalars65968W0.SourceUpper,SourceScalars65968W0.CoeffA,SourceScalars65968W0.CoeffB,SourceScalars65968W0.CoeffC] at hb ⊢
    exact hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment65968W1.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀ (by simpa [Witness,SourceScalars65968W1.Witness] using hW)
    norm_num [G,Fee,CoeffA,CoeffB,CoeffC,SourceScalars65968W1.G,
      SourceScalars65968W1.SourceUpper,SourceScalars65968W1.CoeffA,SourceScalars65968W1.CoeffB,SourceScalars65968W1.CoeffC] at hb ⊢
    exact hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment65968W2.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀ (by simpa [Witness,SourceScalars65968W2.Witness] using hW)
    norm_num [G,Fee,CoeffA,CoeffB,CoeffC,SourceScalars65968W2.G,
      SourceScalars65968W2.SourceUpper,SourceScalars65968W2.CoeffA,SourceScalars65968W2.CoeffB,SourceScalars65968W2.CoeffC] at hb ⊢
    exact hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment65968W3.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀ (by simpa [Witness,SourceScalars65968W3.Witness] using hW)
    norm_num [G,Fee,CoeffA,CoeffB,CoeffC,SourceScalars65968W3.G,
      SourceScalars65968W3.SourceUpper,SourceScalars65968W3.CoeffA,SourceScalars65968W3.CoeffB,SourceScalars65968W3.CoeffC] at hb ⊢
    exact hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment65968W4.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀ (by simpa [Witness,SourceScalars65968W4.Witness] using hW)
    norm_num [G,Fee,CoeffA,CoeffB,CoeffC,SourceScalars65968W4.G,
      SourceScalars65968W4.SourceUpper,SourceScalars65968W4.CoeffA,SourceScalars65968W4.CoeffB,SourceScalars65968W4.CoeffC] at hb ⊢
    exact hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment65968W5.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀ (by simpa [Witness,SourceScalars65968W5.Witness] using hW)
    norm_num [G,Fee,CoeffA,CoeffB,CoeffC,SourceScalars65968W5.G,
      SourceScalars65968W5.SourceUpper,SourceScalars65968W5.CoeffA,SourceScalars65968W5.CoeffB,SourceScalars65968W5.CoeffC] at hb ⊢
    exact hb
  · obtain ⟨A₀,hA₀,hW⟩ := hwitness (by decide)
    have hb := SourcePayment65968W6.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF hA₀ (by simpa [Witness,SourceData67702W9.Witness] using hW)
    norm_num [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W9.G,
      SourceData67702W9.SourceUpper,SourceData67702W9.CoeffA,SourceData67702W9.CoeffB,SourceData67702W9.CoeffC,SourcePayment65968W6.SourceUpper] at hb ⊢
    exact hb
  · have hb := SourcePayment65968W7.actual_inner_source
      (by simpa [info] using hlo) (by simpa [info] using hhi)
      hlegal hbad (by simpa [info] using hsize) hsparse hlegalF hAF
    norm_num [G,Fee,CoeffA,CoeffB,CoeffC,SourceData67702W10.G,
      SourceData67702W10.SourceUpper,SourceData67702W10.CoeffA,SourceData67702W10.CoeffB,SourceData67702W10.CoeffC,SourcePayment65968W7.SourceUpper] at hb ⊢
    exact hb

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment65968
