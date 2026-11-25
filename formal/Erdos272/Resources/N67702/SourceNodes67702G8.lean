module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G3
public import Erdos272.Arithmetic.N67702.RunChecks67702G3
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G2
public import Erdos272.Resources.N67702.SourceNodes67702G3
public import Erdos272.Resources.N67702.SourceNodes67702G4
public import Erdos272.Resources.N67702.SourceNodes67702G7
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G1

@[expose] public section

namespace JSP233.SourceNodes67702G8
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node128 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G3.plan128
  CorrelatedChecks67702G3.checked128 SourceNodes67702G7.node127
  (by decide) (by decide) (by decide)

def node129 : CertifiedContract := ⟨⟨314,1,29790⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked129
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node130 : CertifiedContract where
  contract := ⟨80,39,31758⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan038)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked038)
      SourceNodes67702G2.node038 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node131 : CertifiedContract where
  contract := ⟨80,42,35054⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan039)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked039)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node132 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G3.plan132
  CorrelatedChecks67702G3.checked132 SourceNodes67702G7.node127
  (by decide) (by decide) (by decide)

def node133 : CertifiedContract where
  contract := ⟨80,45,37812⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan040)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked040)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node134 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G3.plan134
  CorrelatedChecks67702G3.checked134 SourceNodes67702G7.node127
  (by decide) (by decide) (by decide)

def node135 : CertifiedContract := ⟨⟨354,1,37820⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked135
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node136 : CertifiedContract where
  contract := ⟨80,47,39982⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan041)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked041)
      SourceNodes67702G3.node053 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node137 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G3.plan137
  CorrelatedChecks67702G3.checked137 SourceNodes67702G3.node058
  (by decide) (by decide) (by decide)

def node138 : CertifiedContract := ⟨⟨365,1,40262⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked138
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node139 : CertifiedContract where
  contract := ⟨80,49,42568⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan042)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked042)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node140 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G3.plan140
  CorrelatedChecks67702G3.checked140 SourceNodes67702G4.node069
  (by decide) (by decide) (by decide)

def node141 : CertifiedContract where
  contract := ⟨80,51,44834⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan043)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked043)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node142 : CertifiedContract where
  contract := ⟨80,52,45928⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan044)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked044)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node143 : CertifiedContract where
  contract := ⟨132,11,46400⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=124) (by decide)
      hN hground hS hsize hdefect

end
end JSP233.SourceNodes67702G8
