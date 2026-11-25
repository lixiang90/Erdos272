module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G7
public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G8
public import Erdos272.Arithmetic.N67702.RunChecks67702G6
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceAtlas86412
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G1
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

namespace JSP233.SourceNodes67702G16
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node256 : CertifiedContract where
  contract := ⟨269,1,21762⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas86412.actual_source (i:=21) (by decide)
      hN hground hS hsize hdefect

def node257 : CertifiedContract where
  contract := ⟨83,34,28906⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan086)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked086)
      SourceNodes67702G1.node020 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node258 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G7.plan258
  CorrelatedChecks67702G7.checked258 SourceNodes67702G16.node257
  (by decide) (by decide) (by decide)

def node259 : CertifiedContract where
  contract := ⟨83,34,27744⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan087)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked087)
      SourceNodes67702G1.node016 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node260 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G7.plan260
  CorrelatedChecks67702G7.checked260 SourceNodes67702G2.node032
  (by decide) (by decide) (by decide)

def node261 : CertifiedContract where
  contract := ⟨83,38,32942⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan088)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked088)
      SourceNodes67702G2.node038 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node262 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G7.plan262
  CorrelatedChecks67702G7.checked262 SourceNodes67702G7.node127
  (by decide) (by decide) (by decide)

def node263 : CertifiedContract := ⟨⟨331,1,33104⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked263
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node264 : CertifiedContract where
  contract := ⟨87,39,36214⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=44) (by decide)
      hN hground hS hsize hdefect

def node265 : CertifiedContract where
  contract := ⟨83,40,34970⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan089)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked089)
      SourceNodes67702G16.node264 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node266 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G8.plan266
  CorrelatedChecks67702G8.checked266 SourceNodes67702G7.node127
  (by decide) (by decide) (by decide)

def node267 : CertifiedContract where
  contract := ⟨83,43,38414⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan090)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked090)
      SourceNodes67702G3.node053 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node268 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G8.plan268
  CorrelatedChecks67702G8.checked268 SourceNodes67702G12.node207
  (by decide) (by decide) (by decide)

def node269 : CertifiedContract := ⟨⟨357,1,38464⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked269
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node270 : CertifiedContract where
  contract := ⟨83,46,41812⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan091)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked091)
      SourceNodes67702G3.node056 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node271 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G8.plan271
  CorrelatedChecks67702G8.checked271 SourceNodes67702G12.node207
  (by decide) (by decide) (by decide)

end
end JSP233.SourceNodes67702G16
