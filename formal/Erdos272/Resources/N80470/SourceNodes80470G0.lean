module

public import Erdos272.Arithmetic.N80470.CorrelatedChecks80470
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N158375.RowSources158375
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N86412.SourceAtlas86412
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N80470.SourceStrictRunContracts80470
public import Erdos272.Resources.N80470.SourceUniform80470

@[expose] public section

namespace JSP233.SourceNodes80470G0
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node000 : CertifiedContract := SourceUniform80470.uniform 0 (by decide)

def node001 : CertifiedContract := SourceStrictRunContracts80470.run 0 (by decide)

def node002 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks80470.plan002)
    (CorrelatedChecks80470.checked002) SourceNodes80470G0.node001
    (by decide) (by decide) (by decide)

def node003 : CertifiedContract where
  contract := ⟨284,1,24304⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=14) (by decide)
      hN hground hS hsize hdefect

def node004 : CertifiedContract := SourceStrictRunContracts80470.run 1 (by decide)

def node005 : CertifiedContract where
  contract := ⟨124,11,38234⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact CorrelatedSource158375.actual_plan_source (SourceQueryData158375.query 108)
      (SourceQueryData158375.conditions (by decide)) (RowSources158375.floors (by decide))
      hN hground hS hsize hdefect

def node006 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks80470.plan006)
    (CorrelatedChecks80470.checked006) SourceNodes80470G0.node005
    (by decide) (by decide) (by decide)

def node007 : CertifiedContract := SourceUniform80470.uniform 1 (by decide)

def node008 : CertifiedContract := SourceStrictRunContracts80470.run 2 (by decide)

def node009 : CertifiedContract where
  contract := ⟨130,12,48484⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=75) (by decide)
      hN hground hS hsize hdefect

def node010 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks80470.plan010)
    (CorrelatedChecks80470.checked010) SourceNodes80470G0.node009
    (by decide) (by decide) (by decide)

def node011 : CertifiedContract := SourceUniform80470.uniform 2 (by decide)

def node012 : CertifiedContract := SourceStrictRunContracts80470.run 3 (by decide)

def node013 : CertifiedContract where
  contract := ⟨132,14,56546⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=55) (by decide)
      hN hground hS hsize hdefect

def node014 : CertifiedContract :=
  SourceCorrelated86412.dynamic (CorrelatedChecks80470.plan014)
    (CorrelatedChecks80470.checked014) SourceNodes80470G0.node013
    (by decide) (by decide) (by decide)

def node015 : CertifiedContract where
  contract := ⟨431,1,56094⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas86412.actual_source (i:=96) (by decide)
      hN hground hS hsize hdefect

end
end JSP233.SourceNodes80470G0
