module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G4
public import Erdos272.Arithmetic.N67702.RunChecks67702G3
public import Erdos272.Arithmetic.N67702.RunChecks67702G4
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N88404.SourceAtlas88404
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G0
public import Erdos272.Resources.N67702.SourceNodes67702G1
public import Erdos272.Resources.N67702.SourceNodes67702G2
public import Erdos272.Resources.N67702.SourceNodes67702G9
public import Erdos272.Resources.N80470.SourceNodes80470G1
public import Erdos272.Resources.N82427.SourceNodes82427G8
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G1

@[expose] public section

namespace JSP233.SourceNodes67702G10
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node160 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G4.plan160
  CorrelatedChecks67702G4.checked160 SourceNodes67702G9.node159
  (by decide) (by decide) (by decide)

def node161 : CertifiedContract := ⟨⟨251,1,19022⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked161
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node162 : CertifiedContract where
  contract := ⟨92,28,31411⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i:=218) (by decide)
      hN hground hS hsize hdefect

def node163 : CertifiedContract where
  contract := ⟨80,28,21348⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan050)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked050)
      SourceNodes67702G10.node162 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node164 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G4.plan164
  CorrelatedChecks67702G4.checked164 SourceNodes67702G10.node163
  (by decide) (by decide) (by decide)

def node165 : CertifiedContract := SourceNodes80470G1.node027

def node166 : CertifiedContract where
  contract := ⟨80,31,24246⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan051)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked051)
      SourceNodes67702G0.node008 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node167 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G4.plan167
  CorrelatedChecks67702G4.checked167 SourceNodes67702G0.node008
  (by decide) (by decide) (by decide)

def node168 : CertifiedContract := ⟨⟨275,1,22806⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked168
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node169 : CertifiedContract where
  contract := ⟨80,34,26924⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan052)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked052)
      SourceNodes67702G0.node012 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node170 : CertifiedContract where
  contract := ⟨80,36,28906⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan053)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked053)
      SourceNodes67702G1.node020 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node171 : CertifiedContract := ⟨⟨309,1,28800⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked171
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node172 : CertifiedContract where
  contract := ⟨80,38,30632⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan054)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked054)
      SourceNodes67702G2.node038 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node173 : CertifiedContract where
  contract := ⟨319,1,30758⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=23) (by decide)
      hN hground hS hsize hdefect

def node174 : CertifiedContract where
  contract := ⟨80,41,33786⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan055)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G4.checked055)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node175 : CertifiedContract := SourceNodes82427G8.node135

end
end JSP233.SourceNodes67702G10
