module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G2
public import Erdos272.Arithmetic.N67702.RunChecks67702G2
public import Erdos272.Resources.N80470.SourceAtlas80470
public import Erdos272.Resources.N86412.SourceAtlas86412
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G0
public import Erdos272.Resources.N67702.SourceNodes67702G2
public import Erdos272.Resources.N67702.SourceNodes67702G3
public import Erdos272.Resources.N80470.SourceNodes80470G1
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G0

@[expose] public section

namespace JSP233.SourceNodes67702G6
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node096 : CertifiedContract where
  contract := ⟨79,45,37122⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan027)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked027)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node097 : CertifiedContract where
  contract := ⟨351,1,37130⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas86412.actual_source (i:=54) (by decide)
      hN hground hS hsize hdefect

def node098 : CertifiedContract where
  contract := ⟨79,49,41374⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan028)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked028)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node099 : CertifiedContract := ⟨⟨371,1,41614⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked099
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node100 : CertifiedContract where
  contract := ⟨80,5,6982⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan029)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked029)
      SourceNodes67702G0.node000 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node101 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G2.plan101
  CorrelatedChecks67702G2.checked101 SourceNodes67702G6.node100
  (by decide) (by decide) (by decide)

def node102 : CertifiedContract := ⟨⟨151,1,6856⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked102
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node103 : CertifiedContract := SourceNodes80470G1.node023

def node104 : CertifiedContract where
  contract := ⟨80,9,10912⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan030)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked030)
      SourceNodes67702G6.node103 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node105 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G2.plan105
  CorrelatedChecks67702G2.checked105 SourceNodes67702G6.node104
  (by decide) (by decide) (by decide)

def node106 : CertifiedContract := ⟨⟨190,1,10786⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked106
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node107 : CertifiedContract where
  contract := ⟨80,18,15450⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan031)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked031)
      SourceNodes67702G0.node008 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node108 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G2.plan108
  CorrelatedChecks67702G2.checked108 SourceNodes67702G6.node107
  (by decide) (by decide) (by decide)

def node109 : CertifiedContract where
  contract := ⟨219,1,14360⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=19) (by decide)
      hN hground hS hsize hdefect

def node110 : CertifiedContract where
  contract := ⟨80,24,18728⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan032)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked032)
      SourceNodes67702G0.node012 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node111 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G2.plan111
  CorrelatedChecks67702G2.checked111 SourceNodes67702G6.node110
  (by decide) (by decide) (by decide)

end
end JSP233.SourceNodes67702G6
