module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G5
public import Erdos272.Arithmetic.N67702.RunChecks67702G4
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G0
public import Erdos272.Resources.N67702.SourceNodes67702G2
public import Erdos272.Resources.N67702.SourceNodes67702G3
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G1

@[expose] public section

namespace JSP233.SourceNodes67702G11
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node176 : CertifiedContract where
  contract := ⟨80,43,35530⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan056)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked056)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node177 : CertifiedContract := ⟨⟨343,1,35544⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked177
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node178 : CertifiedContract where
  contract := ⟨80,44,37120⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan057)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked057)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node179 : CertifiedContract where
  contract := ⟨80,46,39150⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan058)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked058)
      SourceNodes67702G3.node053 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node180 : CertifiedContract where
  contract := ⟨80,48,40964⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan059)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked059)
      SourceNodes67702G3.node056 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node181 : CertifiedContract := ⟨⟨369,1,41160⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked181
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node182 : CertifiedContract where
  contract := ⟨80,50,43668⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan060)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked060)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node183 : CertifiedContract where
  contract := ⟨80,53,47090⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan061)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked061)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node184 : CertifiedContract where
  contract := ⟨133,11,47172⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=92) (by decide)
      hN hground hS hsize hdefect

def node185 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G5.plan185
  CorrelatedChecks67702G5.checked185 SourceNodes67702G11.node184
  (by decide) (by decide) (by decide)

def node186 : CertifiedContract where
  contract := ⟨395,1,47172⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=93) (by decide)
      hN hground hS hsize hdefect

def node187 : CertifiedContract where
  contract := ⟨81,11,12622⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan062)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked062)
      SourceNodes67702G0.node004 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node188 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G5.plan188
  CorrelatedChecks67702G5.checked188 SourceNodes67702G11.node187
  (by decide) (by decide) (by decide)

def node189 : CertifiedContract := ⟨⟨194,1,11324⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked189
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node190 : CertifiedContract where
  contract := ⟨81,24,19256⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan063)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked063)
      SourceNodes67702G0.node012 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node191 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G5.plan191
  CorrelatedChecks67702G5.checked191 SourceNodes67702G11.node190
  (by decide) (by decide) (by decide)

end
end JSP233.SourceNodes67702G11
