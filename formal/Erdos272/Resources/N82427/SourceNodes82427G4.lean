module

public import Erdos272.Arithmetic.N82427.CorrelatedChecks82427
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N130000.RowSources130000
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N86412.SourceAtlas86412
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N82427.SourceNodes82427G3
public import Erdos272.Resources.N82427.SourceStrictRunContracts82427
public import Erdos272.Resources.N82427.SourceUniform82427

@[expose] public section

namespace JSP233.SourceNodes82427G4
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node064 : CertifiedContract := SourceStrictRunContracts82427.run 20 (by decide)

def node065 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan065)
    (CorrelatedChecks82427.checked065) SourceNodes82427G3.node061
    (by decide) (by decide) (by decide)

def node066 : CertifiedContract := SourceUniform82427.uniform 20 (by decide)

def node067 : CertifiedContract := SourceStrictRunContracts82427.run 21 (by decide)

def node068 : CertifiedContract where
  contract := ⟨130,10,40181⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 312)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect

def node069 : CertifiedContract := SourceUniform82427.uniform 21 (by decide)

def node070 : CertifiedContract := SourceStrictRunContracts82427.run 22 (by decide)

def node071 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks82427.plan071)
    (CorrelatedChecks82427.checked071) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node072 : CertifiedContract where
  contract := ⟨366,1,40362⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas86412.actual_source (i:=60) (by decide)
      hN hground hS hsize hdefect

def node073 : CertifiedContract := SourceStrictRunContracts82427.run 23 (by decide)

def node074 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks82427.plan074)
    (CorrelatedChecks82427.checked074) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node075 : CertifiedContract := SourceUniform82427.uniform 22 (by decide)

def node076 : CertifiedContract := SourceStrictRunContracts82427.run 24 (by decide)

def node077 : CertifiedContract :=
  SourceCorrelated86412.dynamic (CorrelatedChecks82427.plan077)
    (CorrelatedChecks82427.checked077) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node078 : CertifiedContract where
  contract := ⟨374,1,42260⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=35) (by decide)
      hN hground hS hsize hdefect

def node079 : CertifiedContract := SourceStrictRunContracts82427.run 25 (by decide)

end
end JSP233.SourceNodes82427G4
