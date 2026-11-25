module

public import Erdos272.Arithmetic.N67702.CorrelatedChecks67702G10
public import Erdos272.Arithmetic.N67702.RunChecks67702G7
public import Erdos272.Resources.N109474.SourceAtlas109474
public import Erdos272.Resources.N118533.SourceAtlas118533
public import Erdos272.Resources.N80470.SourceAtlas80470
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N80470.SourceNodes80470G1
public import Erdos272.Resources.N80470.SourceNodes80470G2
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G2

@[expose] public section

namespace JSP233.SourceNodes67702G20
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node320 : CertifiedContract where
  contract := ⟨87,40,37654⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=47) (by decide)
      hN hground hS hsize hdefect

def node321 : CertifiedContract where
  contract := ⟨152,6,37654⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=48) (by decide)
      hN hground hS hsize hdefect

def node322 : CertifiedContract := SourceNodes80470G2.node039

def node323 : CertifiedContract where
  contract := ⟨152,8,44128⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=33) (by decide)
      hN hground hS hsize hdefect

def node324 : CertifiedContract := SourceNodes80470G2.node042

def node325 : CertifiedContract where
  contract := ⟨87,49,48484⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=74) (by decide)
      hN hground hS hsize hdefect

def node326 : CertifiedContract where
  contract := ⟨150,10,55942⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas80470.actual_source (i:=10) (by decide)
      hN hground hS hsize hdefect

def node327 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G10.plan327
  CorrelatedChecks67702G10.checked327 SourceNodes67702G20.node326
  (by decide) (by decide) (by decide)

def node328 : CertifiedContract where
  contract := ⟨401,1,48484⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=76) (by decide)
      hN hground hS hsize hdefect

def node329 : CertifiedContract := SourceNodes80470G1.node020

def node330 : CertifiedContract where
  contract := ⟨101,30,41472⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas109474.actual_source (i:=92) (by decide)
      hN hground hS hsize hdefect

def node331 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G10.plan331
  CorrelatedChecks67702G10.checked331 SourceNodes67702G20.node330
  (by decide) (by decide) (by decide)

def node332 : CertifiedContract := ⟨⟨362,1,39614⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked332
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node333 : CertifiedContract where
  contract := ⟨104,43,52652⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas118533.actual_source (i:=12) (by decide)
      hN hground hS hsize hdefect

def node334 : CertifiedContract where
  contract := ⟨101,44,52652⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan RunPlans67702.plan106)
      (StrictRunNumericBridge86412.conditions_sound RunChecks67702G7.checked106)
      SourceNodes67702G20.node333 (by decide) (by decide) (by decide)
      hN hground hS hsize hdefect

def node335 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks67702G10.plan335
  CorrelatedChecks67702G10.checked335 SourceNodes67702G20.node326
  (by decide) (by decide) (by decide)

end
end JSP233.SourceNodes67702G20
