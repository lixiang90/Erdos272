module

public import Erdos272.Arithmetic.N80470.CorrelatedChecks80470
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N142758.RowSources142758
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N80470.SourceNodes80470G0
public import Erdos272.Resources.N80470.SourceStrictRunContracts80470
public import Erdos272.Resources.N80470.SourceUniform80470

@[expose] public section

namespace JSP233.SourceNodes80470G1
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node016 : CertifiedContract := SourceStrictRunContracts80470.run 4 (by decide)

def node017 : CertifiedContract where
  contract := ⟨115,25,54629⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact CorrelatedSource158375.actual_plan_source (SourceQueryData142758.query 142)
      (SourceQueryData142758.conditions (by decide)) (RowSources142758.floors (by decide))
      hN hground hS hsize hdefect

def node018 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks80470.plan018)
    (CorrelatedChecks80470.checked018) SourceNodes80470G1.node017
    (by decide) (by decide) (by decide)

def node019 : CertifiedContract := SourceUniform80470.uniform 3 (by decide)

def node020 : CertifiedContract where
  contract := ⟨87,1,2240⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=0) (by decide)
      hN hground hS hsize hdefect

def node021 : CertifiedContract where
  contract := ⟨87,4,7988⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=5) (by decide)
      hN hground hS hsize hdefect

def node022 : CertifiedContract where
  contract := ⟨163,1,7988⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=6) (by decide)
      hN hground hS hsize hdefect

def node023 : CertifiedContract where
  contract := ⟨87,9,16092⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=11) (by decide)
      hN hground hS hsize hdefect

def node024 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks80470.plan024)
    (CorrelatedChecks80470.checked024) SourceNodes80470G1.node023
    (by decide) (by decide) (by decide)

def node025 : CertifiedContract := SourceUniform80470.uniform 4 (by decide)

def node026 : CertifiedContract where
  contract := ⟨87,13,20878⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=15) (by decide)
      hN hground hS hsize hdefect

def node027 : CertifiedContract where
  contract := ⟨263,1,20878⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=16) (by decide)
      hN hground hS hsize hdefect

def node028 : CertifiedContract where
  contract := ⟨87,19,25593⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=21) (by decide)
      hN hground hS hsize hdefect

def node029 : CertifiedContract where
  contract := ⟨292,1,25593⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=22) (by decide)
      hN hground hS hsize hdefect

def node030 : CertifiedContract where
  contract := ⟨87,24,27612⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=25) (by decide)
      hN hground hS hsize hdefect

def node031 : CertifiedContract where
  contract := ⟨303,1,27612⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=26) (by decide)
      hN hground hS hsize hdefect

end
end JSP233.SourceNodes80470G1
