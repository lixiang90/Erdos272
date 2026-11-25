module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G9
public import Erdos272.Arithmetic.N67702.RunChecks67702G7
public import Erdos272.Resources.N80470.SourceAtlas80470
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G12
public import Erdos272.Resources.N67702.SourceNodes67702G13
public import Erdos272.Resources.N67702.SourceNodes67702G15
public import Erdos272.Resources.N67702.SourceNodes67702G7
public import Erdos272.Resources.N80470.SourceNodes80470G1
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G2

@[expose] public section

namespace JSP233.SourceNodes67702G19
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node304 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G9.plan304
  CorrelatedChecks67702G9.checked304 SourceNodes67702G7.node127
  (by decide) (by decide) (by decide)

def node305 : CertifiedContract where
  contract := ⟨87,44,42210⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=59) (by decide)
      hN hground hS hsize hdefect

def node306 : CertifiedContract where
  contract := ⟨85,44,41196⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan103)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G7.checked103)
      SourceNodes67702G19.node305 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node307 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G9.plan307
  CorrelatedChecks67702G9.checked307 SourceNodes67702G12.node207
  (by decide) (by decide) (by decide)

def node308 : CertifiedContract := ⟨⟨370,1,41304⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked308
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node309 : CertifiedContract where
  contract := ⟨85,50,48056⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan104)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G7.checked104)
      SourceNodes67702G13.node217 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node310 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G9.plan310
  CorrelatedChecks67702G9.checked310 SourceNodes67702G12.node207
  (by decide) (by decide) (by decide)

def node311 : CertifiedContract where
  contract := ⟨86,54,54522⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=12) (by decide)
      hN hground hS hsize hdefect

def node312 : CertifiedContract where
  contract := ⟨85,54,53332⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan105)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G7.checked105)
      SourceNodes67702G19.node311 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node313 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G9.plan313
  CorrelatedChecks67702G9.checked313 SourceNodes67702G15.node241
  (by decide) (by decide) (by decide)

def node314 : CertifiedContract := ⟨⟨421,1,53654⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked314
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node315 : CertifiedContract := ⟨⟨85,1,2144⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked315
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node316 : CertifiedContract where
  contract := ⟨87,15,22830⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=17) (by decide)
      hN hground hS hsize hdefect

def node317 : CertifiedContract where
  contract := ⟨276,1,22830⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=18) (by decide)
      hN hground hS hsize hdefect

def node318 : CertifiedContract := SourceNodes80470G1.node030

def node319 : CertifiedContract := SourceNodes80470G1.node031

end
end JSP233.SourceNodes67702G19
