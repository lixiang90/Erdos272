module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G0
public import Erdos272.Arithmetic.N67702.RunChecks67702G1
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G0
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G0

@[expose] public section

namespace JSP233.SourceNodes67702G1
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node016 : CertifiedContract where
  contract := ⟨87,27,27744⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=27) (by decide)
      hN hground hS hsize hdefect

def node017 : CertifiedContract where
  contract := ⟨79,27,19452⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan004)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked004)
      SourceNodes67702G1.node016 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node018 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G0.plan018
  CorrelatedChecks67702G0.checked018 SourceNodes67702G1.node017
  (by decide) (by decide) (by decide)

def node019 : CertifiedContract where
  contract := ⟨248,1,18491⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=14) (by decide)
      hN hground hS hsize hdefect

def node020 : CertifiedContract where
  contract := ⟨87,34,28906⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=29) (by decide)
      hN hground hS hsize hdefect

def node021 : CertifiedContract where
  contract := ⟨79,34,26546⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan005)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked005)
      SourceNodes67702G1.node020 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node022 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G0.plan022
  CorrelatedChecks67702G0.checked022 SourceNodes67702G1.node021
  (by decide) (by decide) (by decide)

def node023 : CertifiedContract := ⟨⟨257,1,19946⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked023
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node024 : CertifiedContract where
  contract := ⟨79,28,21080⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan006)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked006)
      SourceNodes67702G0.node008 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node025 : CertifiedContract where
  contract := ⟨130,8,34966⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=42) (by decide)
      hN hground hS hsize hdefect

def node026 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G0.plan026
  CorrelatedChecks67702G0.checked026 SourceNodes67702G1.node025
  (by decide) (by decide) (by decide)

def node027 : CertifiedContract := ⟨⟨265,1,21182⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked027
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node028 : CertifiedContract where
  contract := ⟨79,32,24246⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan007)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked007)
      SourceNodes67702G0.node008 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node029 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G0.plan029
  CorrelatedChecks67702G0.checked029 SourceNodes67702G0.node008
  (by decide) (by decide) (by decide)

def node030 : CertifiedContract := ⟨⟨281,1,23858⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked030
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node031 : CertifiedContract where
  contract := ⟨79,34,26546⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan008)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked008)
      SourceNodes67702G0.node012 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

end
end JSP233.SourceNodes67702G1
