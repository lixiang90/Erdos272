module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G5
public import Erdos272.Arithmetic.N67702.RunChecks67702G4
public import Erdos272.Arithmetic.N67702.RunChecks67702G5
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G0
public import Erdos272.Resources.N67702.SourceNodes67702G1
public import Erdos272.Resources.N67702.SourceNodes67702G2
public import Erdos272.Resources.N67702.SourceNodes67702G3
public import Erdos272.Resources.N67702.SourceNodes67702G7
public import Erdos272.Resources.N80470.SourceNodes80470G0
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G1

@[expose] public section

namespace JSP233.SourceNodes67702G12
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node192 : CertifiedContract := ⟨⟨253,1,19312⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked192
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node193 : CertifiedContract where
  contract := ⟨81,34,27252⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan064)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked064)
      SourceNodes67702G1.node020 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node194 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G5.plan194
  CorrelatedChecks67702G5.checked194 SourceNodes67702G12.node193
  (by decide) (by decide) (by decide)

def node195 : CertifiedContract := ⟨⟨269,1,21862⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked195
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node196 : CertifiedContract where
  contract := ⟨81,34,27252⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan065)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked065)
      SourceNodes67702G0.node012 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node197 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G5.plan197
  CorrelatedChecks67702G5.checked197 SourceNodes67702G2.node032
  (by decide) (by decide) (by decide)

def node198 : CertifiedContract := ⟨⟨297,1,26608⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked198
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node199 : CertifiedContract where
  contract := ⟨81,36,30008⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan066)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked066)
      SourceNodes67702G7.node125 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node200 : CertifiedContract := ⟨⟨313,1,29634⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked200
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node201 : CertifiedContract where
  contract := ⟨81,39,32444⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan067)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked067)
      SourceNodes67702G2.node038 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node202 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G5.plan202
  CorrelatedChecks67702G5.checked202 SourceNodes67702G7.node127
  (by decide) (by decide) (by decide)

def node203 : CertifiedContract where
  contract := ⟨329,1,32658⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=78) (by decide)
      hN hground hS hsize hdefect

def node204 : CertifiedContract where
  contract := ⟨81,42,35698⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan068)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked068)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node205 : CertifiedContract := ⟨⟨344,1,35712⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked205
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node206 : CertifiedContract where
  contract := ⟨81,45,38896⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan069)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked069)
      SourceNodes67702G3.node053 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node207 : CertifiedContract := SourceNodes80470G0.node009

end
end JSP233.SourceNodes67702G12
