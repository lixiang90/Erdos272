module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G9
public import Erdos272.Arithmetic.N67702.RunChecks67702G6
public import Erdos272.Arithmetic.N67702.RunChecks67702G7
public import Erdos272.Resources.N80470.SourceAtlas80470
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G0
public import Erdos272.Resources.N67702.SourceNodes67702G1
public import Erdos272.Resources.N67702.SourceNodes67702G12
public import Erdos272.Resources.N67702.SourceNodes67702G15
public import Erdos272.Resources.N67702.SourceNodes67702G2
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G2

@[expose] public section

namespace JSP233.SourceNodes67702G18
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node288 : CertifiedContract := ⟨⟨360,1,39094⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked288
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node289 : CertifiedContract where
  contract := ⟨87,48,47882⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=35) (by decide)
      hN hground hS hsize hdefect

def node290 : CertifiedContract where
  contract := ⟨84,48,44924⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan098)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked098)
      SourceNodes67702G18.node289 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node291 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G9.plan291
  CorrelatedChecks67702G9.checked291 SourceNodes67702G12.node207
  (by decide) (by decide) (by decide)

def node292 : CertifiedContract where
  contract := ⟨87,52,52528⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=41) (by decide)
      hN hground hS hsize hdefect

def node293 : CertifiedContract where
  contract := ⟨84,53,51128⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan099)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked099)
      SourceNodes67702G18.node292 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node294 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G9.plan294
  CorrelatedChecks67702G9.checked294 SourceNodes67702G15.node241
  (by decide) (by decide) (by decide)

def node295 : CertifiedContract where
  contract := ⟨412,1,51138⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=96) (by decide)
      hN hground hS hsize hdefect

def node296 : CertifiedContract := ⟨⟨84,1,2082⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked296
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node297 : CertifiedContract where
  contract := ⟨85,18,17936⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan100)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G7.checked100)
      SourceNodes67702G0.node008 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node298 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G9.plan298
  CorrelatedChecks67702G9.checked298 SourceNodes67702G18.node297
  (by decide) (by decide) (by decide)

def node299 : CertifiedContract where
  contract := ⟨243,1,17810⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=10) (by decide)
      hN hground hS hsize hdefect

def node300 : CertifiedContract where
  contract := ⟨85,34,28906⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan101)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G7.checked101)
      SourceNodes67702G1.node020 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node301 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G9.plan301
  CorrelatedChecks67702G9.checked301 SourceNodes67702G18.node300
  (by decide) (by decide) (by decide)

def node302 : CertifiedContract := ⟨⟨290,1,25348⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked302
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node303 : CertifiedContract where
  contract := ⟨85,38,34866⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan102)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G7.checked102)
      SourceNodes67702G2.node038 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

end
end JSP233.SourceNodes67702G18
