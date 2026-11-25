module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G1
public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G2
public import Erdos272.Arithmetic.N67702.RunChecks67702G1
public import Erdos272.Arithmetic.N67702.RunChecks67702G2
public import Erdos272.Resources.N80470.SourceAtlas80470
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G3
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G0

@[expose] public section

namespace JSP233.SourceNodes67702G4
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node064 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G1.plan064
  CorrelatedChecks67702G1.checked064 SourceNodes67702G3.node063
  (by decide) (by decide) (by decide)

def node065 : CertifiedContract := ⟨⟨376,1,42646⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked065
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node066 : CertifiedContract where
  contract := ⟨79,51,43696⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan018)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked018)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node067 : CertifiedContract := ⟨⟨381,1,43858⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked067
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node068 : CertifiedContract where
  contract := ⟨79,52,44804⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan019)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked019)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node069 : CertifiedContract where
  contract := ⟨130,11,45310⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=66) (by decide)
      hN hground hS hsize hdefect

def node070 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G1.plan070
  CorrelatedChecks67702G1.checked070 SourceNodes67702G4.node069
  (by decide) (by decide) (by decide)

def node071 : CertifiedContract := ⟨⟨386,1,44986⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked071
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node072 : CertifiedContract := ⟨⟨79,1,1854⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked072
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node073 : CertifiedContract where
  contract := ⟨87,4,7988⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=16) (by decide)
      hN hground hS hsize hdefect

def node074 : CertifiedContract where
  contract := ⟨79,4,5632⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan020)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked020)
      SourceNodes67702G4.node073 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node075 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G1.plan075
  CorrelatedChecks67702G1.checked075 SourceNodes67702G4.node074
  (by decide) (by decide) (by decide)

def node076 : CertifiedContract := ⟨⟨131,1,5152⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked076
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node077 : CertifiedContract where
  contract := ⟨87,7,13160⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=9) (by decide)
      hN hground hS hsize hdefect

def node078 : CertifiedContract where
  contract := ⟨79,7,8760⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan021)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked021)
      SourceNodes67702G4.node077 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node079 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G2.plan079
  CorrelatedChecks67702G2.checked079 SourceNodes67702G4.node078
  (by decide) (by decide) (by decide)

end
end JSP233.SourceNodes67702G4
