module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G0
public import Erdos272.Arithmetic.N67702.RunChecks67702G0
public import Erdos272.Resources.N80470.SourceAtlas80470
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G0

@[expose] public section

namespace JSP233.SourceNodes67702G0
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node000 : CertifiedContract where
  contract := ⟨87,5,9790⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=7) (by decide)
      hN hground hS hsize hdefect

def node001 : CertifiedContract where
  contract := ⟨79,5,6744⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan000)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G0.checked000)
      SourceNodes67702G0.node000 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node002 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G0.plan002
  CorrelatedChecks67702G0.checked002 SourceNodes67702G0.node001
  (by decide) (by decide) (by decide)

def node003 : CertifiedContract := ⟨⟨149,1,6668⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked003
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node004 : CertifiedContract where
  contract := ⟨87,11,18491⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=13) (by decide)
      hN hground hS hsize hdefect

def node005 : CertifiedContract where
  contract := ⟨79,11,11902⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan001)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G0.checked001)
      SourceNodes67702G0.node004 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node006 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G0.plan006
  CorrelatedChecks67702G0.checked006 SourceNodes67702G0.node005
  (by decide) (by decide) (by decide)

def node007 : CertifiedContract := ⟨⟨189,1,10714⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked007
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node008 : CertifiedContract where
  contract := ⟨86,18,24246⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=1) (by decide)
      hN hground hS hsize hdefect

def node009 : CertifiedContract where
  contract := ⟨79,18,14678⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan002)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G0.checked002)
      SourceNodes67702G0.node008 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node010 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G0.plan010
  CorrelatedChecks67702G0.checked010 SourceNodes67702G0.node009
  (by decide) (by decide) (by decide)

def node011 : CertifiedContract := ⟨⟨215,1,13926⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked011
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node012 : CertifiedContract where
  contract := ⟨87,24,27612⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=24) (by decide)
      hN hground hS hsize hdefect

def node013 : CertifiedContract where
  contract := ⟨79,24,18200⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan003)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G0.checked003)
      SourceNodes67702G0.node012 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node014 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G0.plan014
  CorrelatedChecks67702G0.checked014 SourceNodes67702G0.node013
  (by decide) (by decide) (by decide)

def node015 : CertifiedContract := ⟨⟨235,1,16638⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked015
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

end
end JSP233.SourceNodes67702G0
