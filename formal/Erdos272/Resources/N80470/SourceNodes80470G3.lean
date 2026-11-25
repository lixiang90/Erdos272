module

public import Erdos272.Arithmetic.N80470.CorrelatedChecks80470
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N80470.SourceNodes80470G2
public import Erdos272.Resources.N80470.SourceStrictRunContracts80470
public import Erdos272.Resources.N80470.SourceUniform80470

@[expose] public section

namespace JSP233.SourceNodes80470G3
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node048 : CertifiedContract where
  contract := ⟨130,13,50284⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=78) (by decide)
      hN hground hS hsize hdefect

def node049 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks80470.plan049)
    (CorrelatedChecks80470.checked049) SourceNodes80470G3.node048
    (by decide) (by decide) (by decide)

def node050 : CertifiedContract where
  contract := ⟨409,1,50284⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=79) (by decide)
      hN hground hS hsize hdefect

def node051 : CertifiedContract where
  contract := ⟨87,52,52528⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=83) (by decide)
      hN hground hS hsize hdefect

def node052 : CertifiedContract where
  contract := ⟨130,14,52528⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=84) (by decide)
      hN hground hS hsize hdefect

def node053 : CertifiedContract :=
  SourceCorrelated86412.dynamic (CorrelatedChecks80470.plan053)
    (CorrelatedChecks80470.checked053) SourceNodes80470G3.node052
    (by decide) (by decide) (by decide)

def node054 : CertifiedContract where
  contract := ⟨417,1,52528⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=85) (by decide)
      hN hground hS hsize hdefect

def node055 : CertifiedContract where
  contract := ⟨87,54,55262⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=89) (by decide)
      hN hground hS hsize hdefect

def node056 : CertifiedContract where
  contract := ⟨130,14,55262⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=90) (by decide)
      hN hground hS hsize hdefect

def node057 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks80470.plan057)
    (CorrelatedChecks80470.checked057) SourceNodes80470G3.node056
    (by decide) (by decide) (by decide)

def node058 : CertifiedContract where
  contract := ⟨428,1,55262⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=91) (by decide)
      hN hground hS hsize hdefect

end
end JSP233.SourceNodes80470G3
