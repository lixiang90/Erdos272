module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G4
public import Erdos272.Arithmetic.N67702.RunChecks67702G3
public import Erdos272.Resources.N80470.SourceAtlas80470
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N67702.SourceNodes67702G0
public import Erdos272.Resources.N67702.SourceNodes67702G1
public import Erdos272.Resources.N67702.SourceNodes67702G4
public import Erdos272.Resources.N67702.SourceNodes67702G5
public import Erdos272.Resources.N67702.SourceNodes67702G8
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G1

@[expose] public section

namespace JSP233.SourceNodes67702G9
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node144 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G4.plan144
  CorrelatedChecks67702G4.checked144 SourceNodes67702G8.node143
  (by decide) (by decide) (by decide)

def node145 : CertifiedContract where
  contract := ⟨391,1,46176⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=70) (by decide)
      hN hground hS hsize hdefect

def node146 : CertifiedContract := ⟨⟨80,1,1886⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked146
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node147 : CertifiedContract where
  contract := ⟨80,4,5830⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan045)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked045)
      SourceNodes67702G4.node073 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node148 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G4.plan148
  CorrelatedChecks67702G4.checked148 SourceNodes67702G9.node147
  (by decide) (by decide) (by decide)

def node149 : CertifiedContract where
  contract := ⟨87,8,14360⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=18) (by decide)
      hN hground hS hsize hdefect

def node150 : CertifiedContract where
  contract := ⟨80,8,10044⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan046)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked046)
      SourceNodes67702G9.node149 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node151 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G4.plan151
  CorrelatedChecks67702G4.checked151 SourceNodes67702G9.node150
  (by decide) (by decide) (by decide)

def node152 : CertifiedContract := ⟨⟨179,1,9652⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked152
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node153 : CertifiedContract where
  contract := ⟨80,11,12410⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan047)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked047)
      SourceNodes67702G0.node004 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node154 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G4.plan154
  CorrelatedChecks67702G4.checked154 SourceNodes67702G9.node153
  (by decide) (by decide) (by decide)

def node155 : CertifiedContract := ⟨⟨202,1,12262⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked155
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node156 : CertifiedContract where
  contract := ⟨80,21,16282⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan048)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked048)
      SourceNodes67702G5.node083 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node157 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G4.plan157
  CorrelatedChecks67702G4.checked157 SourceNodes67702G9.node156
  (by decide) (by decide) (by decide)

def node158 : CertifiedContract := ⟨⟨233,1,16384⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G1.checked158
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node159 : CertifiedContract where
  contract := ⟨80,27,19600⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan049)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G3.checked049)
      SourceNodes67702G1.node016 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

end
end JSP233.SourceNodes67702G9
