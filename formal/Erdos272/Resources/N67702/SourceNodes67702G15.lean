module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G7
public import Erdos272.Arithmetic.N67702.RunChecks67702G5
public import Erdos272.Arithmetic.N67702.RunChecks67702G6
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G0
public import Erdos272.Resources.N67702.SourceNodes67702G1
public import Erdos272.Resources.N67702.SourceNodes67702G13
public import Erdos272.Resources.N80470.SourceNodes80470G0
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G1

@[expose] public section

namespace JSP233.SourceNodes67702G15
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node240 : CertifiedContract where
  contract := ⟨82,53,48884⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan081)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked081)
      SourceNodes67702G13.node217 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node241 : CertifiedContract := SourceNodes80470G0.node013

def node242 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G7.plan242
  CorrelatedChecks67702G7.checked242 SourceNodes67702G15.node241
  (by decide) (by decide) (by decide)

def node243 : CertifiedContract := ⟨⟨403,1,49166⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked243
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node244 : CertifiedContract := ⟨⟨82,1,1978⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked244
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node245 : CertifiedContract where
  contract := ⟨83,5,7476⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan082)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked082)
      SourceNodes67702G0.node000 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node246 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G7.plan246
  CorrelatedChecks67702G7.checked246 SourceNodes67702G15.node245
  (by decide) (by decide) (by decide)

def node247 : CertifiedContract := ⟨⟨155,1,7200⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked247
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node248 : CertifiedContract where
  contract := ⟨83,11,13368⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan083)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked083)
      SourceNodes67702G0.node004 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node249 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G7.plan249
  CorrelatedChecks67702G7.checked249 SourceNodes67702G15.node248
  (by decide) (by decide) (by decide)

def node250 : CertifiedContract where
  contract := ⟨210,1,13160⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=10) (by decide)
      hN hground hS hsize hdefect

def node251 : CertifiedContract where
  contract := ⟨83,24,20300⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan084)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked084)
      SourceNodes67702G0.node012 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node252 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G7.plan252
  CorrelatedChecks67702G7.checked252 SourceNodes67702G15.node251
  (by decide) (by decide) (by decide)

def node253 : CertifiedContract := ⟨⟨249,1,18674⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked253
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node254 : CertifiedContract where
  contract := ⟨83,27,21712⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan085)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked085)
      SourceNodes67702G1.node016 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node255 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G7.plan255
  CorrelatedChecks67702G7.checked255 SourceNodes67702G15.node254
  (by decide) (by decide) (by decide)

end
end JSP233.SourceNodes67702G15
