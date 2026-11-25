module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G1
public import Erdos272.Arithmetic.N67702.RunChecks67702G1
public import Erdos272.Resources.N80470.SourceAtlas80470
public import Erdos272.Resources.N86412.SourceAtlas86412
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G1
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G0

@[expose] public section

namespace JSP233.SourceNodes67702G2
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node032 : CertifiedContract where
  contract := ⟨150,7,38220⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=4) (by decide)
      hN hground hS hsize hdefect

def node033 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G1.plan033
  CorrelatedChecks67702G1.checked033 SourceNodes67702G2.node032
  (by decide) (by decide) (by decide)

def node034 : CertifiedContract := ⟨⟨294,1,26056⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked034
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node035 : CertifiedContract where
  contract := ⟨79,36,28472⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan009)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked009)
      SourceNodes67702G1.node020 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node036 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G1.plan036
  CorrelatedChecks67702G1.checked036 SourceNodes67702G1.node025
  (by decide) (by decide) (by decide)

def node037 : CertifiedContract := ⟨⟨307,1,28478⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked037
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node038 : CertifiedContract where
  contract := ⟨87,38,34966⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=26) (by decide)
      hN hground hS hsize hdefect

def node039 : CertifiedContract where
  contract := ⟨79,38,30114⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan010)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked010)
      SourceNodes67702G2.node038 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node040 : CertifiedContract where
  contract := ⟨317,1,30325⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas86412.actual_source (i:=118) (by decide)
      hN hground hS hsize hdefect

def node041 : CertifiedContract where
  contract := ⟨79,40,31668⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan011)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked011)
      SourceNodes67702G2.node038 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node042 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G1.plan042
  CorrelatedChecks67702G1.checked042 SourceNodes67702G1.node025
  (by decide) (by decide) (by decide)

def node043 : CertifiedContract := ⟨⟨325,1,31886⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked043
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node044 : CertifiedContract where
  contract := ⟨86,41,38220⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=3) (by decide)
      hN hground hS hsize hdefect

def node045 : CertifiedContract where
  contract := ⟨79,42,34050⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan012)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked012)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node046 : CertifiedContract := ⟨⟨337,1,34340⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked046
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node047 : CertifiedContract where
  contract := ⟨79,44,36168⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan013)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked013)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

end
end JSP233.SourceNodes67702G2
