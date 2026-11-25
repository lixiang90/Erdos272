module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G1
public import Erdos272.Arithmetic.N67702.RunChecks67702G1
public import Erdos272.Resources.N80470.SourceAtlas80470
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G2
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G0

@[expose] public section

namespace JSP233.SourceNodes67702G3
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node048 : CertifiedContract where
  contract := ⟨132,9,39616⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=118) (by decide)
      hN hground hS hsize hdefect

def node049 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G1.plan049
  CorrelatedChecks67702G1.checked049 SourceNodes67702G3.node048
  (by decide) (by decide) (by decide)

def node050 : CertifiedContract where
  contract := ⟨347,1,36214⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=46) (by decide)
      hN hground hS hsize hdefect

def node051 : CertifiedContract where
  contract := ⟨79,46,37954⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan014)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked014)
      SourceNodes67702G2.node044 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node052 : CertifiedContract := ⟨⟨355,1,38098⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked052
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node053 : CertifiedContract where
  contract := ⟨87,42,40290⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=29) (by decide)
      hN hground hS hsize hdefect

def node054 : CertifiedContract where
  contract := ⟨79,47,39244⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan015)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked015)
      SourceNodes67702G3.node053 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node055 : CertifiedContract := ⟨⟨361,1,39434⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked055
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node056 : CertifiedContract where
  contract := ⟨87,45,44128⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=32) (by decide)
      hN hground hS hsize hdefect

def node057 : CertifiedContract where
  contract := ⟨79,48,40470⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan016)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked016)
      SourceNodes67702G3.node056 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node058 : CertifiedContract where
  contract := ⟨130,10,42210⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=60) (by decide)
      hN hground hS hsize hdefect

def node059 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G1.plan059
  CorrelatedChecks67702G1.checked059 SourceNodes67702G3.node058
  (by decide) (by decide) (by decide)

def node060 : CertifiedContract := ⟨⟨367,1,40746⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G0.checked060
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node061 : CertifiedContract where
  contract := ⟨86,49,48000⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=6) (by decide)
      hN hground hS hsize hdefect

def node062 : CertifiedContract where
  contract := ⟨79,50,42614⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan017)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G1.checked017)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node063 : CertifiedContract where
  contract := ⟨133,10,44088⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=89) (by decide)
      hN hground hS hsize hdefect

end
end JSP233.SourceNodes67702G3
