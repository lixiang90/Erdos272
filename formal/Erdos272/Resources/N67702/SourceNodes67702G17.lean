module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G8
public import Erdos272.Arithmetic.N67702.RunChecks67702G6
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G0
public import Erdos272.Resources.N67702.SourceNodes67702G1
public import Erdos272.Resources.N67702.SourceNodes67702G12
public import Erdos272.Resources.N67702.SourceNodes67702G14
public import Erdos272.Resources.N67702.SourceNodes67702G2
public import Erdos272.Resources.N67702.SourceNodes67702G3
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G2

@[expose] public section

namespace JSP233.SourceNodes67702G17
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node272 : CertifiedContract where
  contract := ⟨83,48,43862⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan092)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked092)
      SourceNodes67702G3.node056 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node273 : CertifiedContract := ⟨⟨382,1,44048⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked273
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node274 : CertifiedContract where
  contract := ⟨83,51,47538⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan093)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked093)
      SourceNodes67702G3.node061 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node275 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G8.plan275
  CorrelatedChecks67702G8.checked275 SourceNodes67702G12.node207
  (by decide) (by decide) (by decide)

def node276 : CertifiedContract := ⟨⟨397,1,47706⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked276
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node277 : CertifiedContract := ⟨⟨83,1,2058⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked277
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node278 : CertifiedContract where
  contract := ⟨84,24,20800⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan094)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked094)
      SourceNodes67702G0.node012 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node279 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G8.plan279
  CorrelatedChecks67702G8.checked279 SourceNodes67702G17.node278
  (by decide) (by decide) (by decide)

def node280 : CertifiedContract := ⟨⟨247,1,18392⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked280
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node281 : CertifiedContract where
  contract := ⟨84,34,28906⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan095)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked095)
      SourceNodes67702G1.node020 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node282 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G8.plan282
  CorrelatedChecks67702G8.checked282 SourceNodes67702G17.node281
  (by decide) (by decide) (by decide)

def node283 : CertifiedContract := ⟨⟨285,1,24512⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked283
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node284 : CertifiedContract where
  contract := ⟨84,37,31910⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan096)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked096)
      SourceNodes67702G14.node228 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node285 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G8.plan285
  CorrelatedChecks67702G8.checked285 SourceNodes67702G2.node032
  (by decide) (by decide) (by decide)

def node286 : CertifiedContract where
  contract := ⟨84,43,39060⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan097)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G6.checked097)
      SourceNodes67702G3.node053 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node287 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G8.plan287
  CorrelatedChecks67702G8.checked287 SourceNodes67702G12.node207
  (by decide) (by decide) (by decide)

end
end JSP233.SourceNodes67702G17
