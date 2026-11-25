module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G2
public import Erdos272.Arithmetic.N67702.RunChecks67702G2
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G0
public import Erdos272.Resources.N67702.SourceNodes67702G1
public import Erdos272.Resources.N67702.SourceNodes67702G2
public import Erdos272.Resources.N67702.SourceNodes67702G3
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G0

@[expose] public section

namespace JSP233.SourceNodes67702G5
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node080 : CertifiedContract := ⟨⟨164,1,8070⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked080
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node081 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G2.plan081
  CorrelatedChecks67702G2.checked081 SourceNodes67702G0.node009
  (by decide) (by decide) (by decide)

def node082 : CertifiedContract := ⟨⟨207,1,12882⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked082
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node083 : CertifiedContract where
  contract := ⟨87,21,26752⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=23) (by decide)
      hN hground hS hsize hdefect

def node084 : CertifiedContract where
  contract := ⟨79,21,15930⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan022)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked022)
      SourceNodes67702G5.node083 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node085 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G2.plan085
  CorrelatedChecks67702G2.checked085 SourceNodes67702G5.node084
  (by decide) (by decide) (by decide)

def node086 : CertifiedContract where
  contract := ⟨223,1,14984⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=8) (by decide)
      hN hground hS hsize hdefect

def node087 : CertifiedContract where
  contract := ⟨79,30,23548⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan023)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked023)
      SourceNodes67702G0.node008 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node088 : CertifiedContract := ⟨⟨270,1,21934⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked088
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node089 : CertifiedContract where
  contract := ⟨79,35,27708⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan024)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked024)
      SourceNodes67702G1.node016 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node090 : CertifiedContract := ⟨⟨303,1,27696⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked090
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node091 : CertifiedContract where
  contract := ⟨79,41,33224⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan025)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked025)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node092 : CertifiedContract := ⟨⟨332,1,33268⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked092
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node093 : CertifiedContract where
  contract := ⟨79,43,35092⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan026)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked026)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node094 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G2.plan094
  CorrelatedChecks67702G2.checked094 SourceNodes67702G3.node048
  (by decide) (by decide) (by decide)

def node095 : CertifiedContract := ⟨⟨341,1,35144⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked095
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

end
end JSP233.SourceNodes67702G5
