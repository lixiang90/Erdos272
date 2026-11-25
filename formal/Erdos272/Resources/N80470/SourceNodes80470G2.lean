module

public import Erdos272.Arithmetic.N80470.CorrelatedChecks80470
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N155716.RowSources155716
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N80470.SourceNodes80470G1
public import Erdos272.Resources.N80470.SourceStrictRunContracts80470
public import Erdos272.Resources.N80470.SourceUniform80470

@[expose] public section

namespace JSP233.SourceNodes80470G2
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node032 : CertifiedContract where
  contract := ⟨87,38,34966⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=41) (by decide)
      hN hground hS hsize hdefect

def node033 : CertifiedContract where
  contract := ⟨166,5,34977⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact CorrelatedSource158375.actual_plan_source (SourceQueryData155716.query 9)
      (SourceQueryData155716.conditions (by decide)) (RowSources155716.floors (by decide))
      hN hground hS hsize hdefect

def node034 : CertifiedContract where
  contract := ⟨341,1,34966⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=43) (by decide)
      hN hground hS hsize hdefect

def node035 : CertifiedContract where
  contract := ⟨87,42,40290⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=53) (by decide)
      hN hground hS hsize hdefect

def node036 : CertifiedContract where
  contract := ⟨130,10,40290⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=54) (by decide)
      hN hground hS hsize hdefect

def node037 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks80470.plan037)
    (CorrelatedChecks80470.checked037) SourceNodes80470G2.node036
    (by decide) (by decide) (by decide)

def node038 : CertifiedContract where
  contract := ⟨366,1,40290⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=55) (by decide)
      hN hground hS hsize hdefect

def node039 : CertifiedContract where
  contract := ⟨87,45,44128⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=62) (by decide)
      hN hground hS hsize hdefect

def node040 : CertifiedContract where
  contract := ⟨130,11,44128⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=63) (by decide)
      hN hground hS hsize hdefect

def node041 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks80470.plan041)
    (CorrelatedChecks80470.checked041) SourceNodes80470G2.node040
    (by decide) (by decide) (by decide)

def node042 : CertifiedContract where
  contract := ⟨383,1,44128⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=64) (by decide)
      hN hground hS hsize hdefect

def node043 : CertifiedContract where
  contract := ⟨87,48,47882⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=71) (by decide)
      hN hground hS hsize hdefect

def node044 : CertifiedContract where
  contract := ⟨130,12,47882⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=72) (by decide)
      hN hground hS hsize hdefect

def node045 : CertifiedContract :=
  SourceCorrelated86412.dynamic (CorrelatedChecks80470.plan045)
    (CorrelatedChecks80470.checked045) SourceNodes80470G2.node044
    (by decide) (by decide) (by decide)

def node046 : CertifiedContract where
  contract := ⟨398,1,47882⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=73) (by decide)
      hN hground hS hsize hdefect

def node047 : CertifiedContract where
  contract := ⟨87,50,50284⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=77) (by decide)
      hN hground hS hsize hdefect

end
end JSP233.SourceNodes80470G2
