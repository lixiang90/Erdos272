module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G6
public import Erdos272.Arithmetic.N67702.RunChecks67702G5
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G0
public import Erdos272.Resources.N67702.SourceNodes67702G12
public import Erdos272.Resources.N67702.SourceNodes67702G2
public import Erdos272.Resources.N67702.SourceNodes67702G3
public import Erdos272.Resources.N67702.SourceNodes67702G7
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G1

@[expose] public section

namespace JSP233.SourceNodes67702G14
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node224 : CertifiedContract where
  contract := ⟨82,24,19766⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan075)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked075)
      SourceNodes67702G0.node012 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node225 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G6.plan225
  CorrelatedChecks67702G6.checked225 SourceNodes67702G14.node224
  (by decide) (by decide) (by decide)

def node226 : CertifiedContract where
  contract := ⟨82,29,23468⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan076)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked076)
      SourceNodes67702G7.node116 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node227 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G6.plan227
  CorrelatedChecks67702G6.checked227 SourceNodes67702G14.node226
  (by decide) (by decide) (by decide)

def node228 : CertifiedContract where
  contract := ⟨87,36,31910⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=35) (by decide)
      hN hground hS hsize hdefect

def node229 : CertifiedContract where
  contract := ⟨82,37,31536⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan077)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked077)
      SourceNodes67702G14.node228 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node230 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G6.plan230
  CorrelatedChecks67702G6.checked230 SourceNodes67702G7.node127
  (by decide) (by decide) (by decide)

def node231 : CertifiedContract := ⟨⟨322,1,31254⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked231
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node232 : CertifiedContract where
  contract := ⟨82,43,37582⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan078)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked078)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node233 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G6.plan233
  CorrelatedChecks67702G6.checked233 SourceNodes67702G7.node127
  (by decide) (by decide) (by decide)

def node234 : CertifiedContract where
  contract := ⟨353,1,37654⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=49) (by decide)
      hN hground hS hsize hdefect

def node235 : CertifiedContract where
  contract := ⟨82,47,41934⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan079)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked079)
      SourceNodes67702G3.node056 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node236 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G6.plan236
  CorrelatedChecks67702G6.checked236 SourceNodes67702G12.node207
  (by decide) (by decide) (by decide)

def node237 : CertifiedContract where
  contract := ⟨82,50,45412⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan080)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked080)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node238 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G6.plan238
  CorrelatedChecks67702G6.checked238 SourceNodes67702G12.node207
  (by decide) (by decide) (by decide)

def node239 : CertifiedContract := ⟨⟨388,1,45428⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked239
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

end
end JSP233.SourceNodes67702G14
