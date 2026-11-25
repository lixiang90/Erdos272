module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G5
public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G6
public import Erdos272.Arithmetic.N67702.RunChecks67702G5
public import Erdos272.Resources.N80470.SourceAtlas80470
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G12
public import Erdos272.Resources.N67702.SourceNodes67702G3
public import Erdos272.Resources.N67702.SourceNodes67702G6
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G1

@[expose] public section

namespace JSP233.SourceNodes67702G13
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node208 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G5.plan208
  CorrelatedChecks67702G5.checked208 SourceNodes67702G12.node207
  (by decide) (by decide) (by decide)

def node209 : CertifiedContract := ⟨⟨359,1,38998⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked209
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node210 : CertifiedContract where
  contract := ⟨81,48,42076⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan070)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked070)
      SourceNodes67702G3.node056 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node211 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G5.plan211
  CorrelatedChecks67702G5.checked211 SourceNodes67702G12.node207
  (by decide) (by decide) (by decide)

def node212 : CertifiedContract := ⟨⟨373,1,42104⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked212
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node213 : CertifiedContract where
  contract := ⟨81,50,44290⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan071)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked071)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node214 : CertifiedContract := ⟨⟨383,1,44428⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked214
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node215 : CertifiedContract where
  contract := ⟨81,52,47000⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan072)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked072)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node216 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G6.plan216
  CorrelatedChecks67702G6.checked216 SourceNodes67702G12.node207
  (by decide) (by decide) (by decide)

def node217 : CertifiedContract where
  contract := ⟨87,50,50284⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=38) (by decide)
      hN hground hS hsize hdefect

def node218 : CertifiedContract where
  contract := ⟨81,53,48094⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan073)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked073)
      SourceNodes67702G13.node217 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node219 : CertifiedContract := ⟨⟨399,1,48118⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked219
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node220 : CertifiedContract := ⟨⟨81,1,1938⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked220
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node221 : CertifiedContract where
  contract := ⟨82,9,11524⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan074)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G5.checked074)
      SourceNodes67702G6.node103 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node222 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G6.plan222
  CorrelatedChecks67702G6.checked222 SourceNodes67702G13.node221
  (by decide) (by decide) (by decide)

def node223 : CertifiedContract := ⟨⟨197,1,11696⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked223
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

end
end JSP233.SourceNodes67702G13
