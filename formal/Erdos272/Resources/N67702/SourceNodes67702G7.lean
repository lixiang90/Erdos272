module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G3
public import Erdos272.Arithmetic.N67702.RunChecks67702G2
public import Erdos272.Arithmetic.N67702.RunChecks67702G3
public import Erdos272.Resources.N80470.SourceAtlas80470
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N94488.SourceAtlas94488
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G1
public import Erdos272.Resources.N67702.SourceNodes67702G2
public import Erdos272.Resources.N80470.SourceNodes80470G0
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G0

@[expose] public section

namespace JSP233.SourceNodes67702G7
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node112 : CertifiedContract := ⟨⟨244,1,17932⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked112
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node113 : CertifiedContract where
  contract := ⟨80,34,26924⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan033)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked033)
      SourceNodes67702G1.node020 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node114 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G3.plan114
  CorrelatedChecks67702G3.checked114 SourceNodes67702G7.node113
  (by decide) (by decide) (by decide)

def node115 : CertifiedContract := ⟨⟨259,1,20244⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked115
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node116 : CertifiedContract where
  contract := ⟨93,29,32413⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas94488.actual_source (i:=29) (by decide)
      hN hground hS hsize hdefect

def node117 : CertifiedContract where
  contract := ⟨80,29,22856⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan034)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked034)
      SourceNodes67702G7.node116 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node118 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G3.plan118
  CorrelatedChecks67702G3.checked118 SourceNodes67702G7.node117
  (by decide) (by decide) (by decide)

def node119 : CertifiedContract := ⟨⟨268,1,21596⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked119
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node120 : CertifiedContract where
  contract := ⟨87,19,25593⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=22) (by decide)
      hN hground hS hsize hdefect

def node121 : CertifiedContract where
  contract := ⟨80,33,25593⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan035)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G2.checked035)
      SourceNodes67702G7.node120 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node122 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G3.plan122
  CorrelatedChecks67702G3.checked122 SourceNodes67702G2.node032
  (by decide) (by decide) (by decide)

def node123 : CertifiedContract := ⟨⟨289,1,25236⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked123
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node124 : CertifiedContract where
  contract := ⟨80,35,27744⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan036)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked036)
      SourceNodes67702G1.node016 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node125 : CertifiedContract where
  contract := ⟨87,35,30026⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=32) (by decide)
      hN hground hS hsize hdefect

def node126 : CertifiedContract where
  contract := ⟨80,37,29678⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan037)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked037)
      SourceNodes67702G7.node125 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node127 : CertifiedContract := SourceNodes80470G0.node005

end
end JSP233.SourceNodes67702G7
