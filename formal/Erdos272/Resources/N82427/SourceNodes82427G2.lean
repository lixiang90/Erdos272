module

public import Erdos272.Arithmetic.N82427.CorrelatedChecks82427
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N86412.SourceAtlas86412
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N82427.SourceNodes82427G1
public import Erdos272.Resources.N82427.SourceStrictRunContracts82427
public import Erdos272.Resources.N82427.SourceUniform82427

@[expose] public section

namespace JSP233.SourceNodes82427G2
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node032 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan032)
    (CorrelatedChecks82427.checked032) SourceNodes82427G1.node031
    (by decide) (by decide) (by decide)

def node033 : CertifiedContract where
  contract := ⟨292,1,25648⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas86412.actual_source (i:=115) (by decide)
      hN hground hS hsize hdefect

def node034 : CertifiedContract := SourceStrictRunContracts82427.run 11 (by decide)

def node035 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan035)
    (CorrelatedChecks82427.checked035) SourceNodes82427G2.node034
    (by decide) (by decide) (by decide)

def node036 : CertifiedContract := SourceUniform82427.uniform 11 (by decide)

def node037 : CertifiedContract := SourceStrictRunContracts82427.run 12 (by decide)

def node038 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan038)
    (CorrelatedChecks82427.checked038) SourceNodes82427G2.node037
    (by decide) (by decide) (by decide)

def node039 : CertifiedContract := SourceUniform82427.uniform 12 (by decide)

def node040 : CertifiedContract := SourceStrictRunContracts82427.run 13 (by decide)

def node041 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan041)
    (CorrelatedChecks82427.checked041) SourceNodes82427G2.node040
    (by decide) (by decide) (by decide)

def node042 : CertifiedContract := SourceUniform82427.uniform 13 (by decide)

def node043 : CertifiedContract := SourceStrictRunContracts82427.run 14 (by decide)

def node044 : CertifiedContract where
  contract := ⟨132,8,33842⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=25) (by decide)
      hN hground hS hsize hdefect

def node045 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks82427.plan045)
    (CorrelatedChecks82427.checked045) SourceNodes82427G2.node044
    (by decide) (by decide) (by decide)

def node046 : CertifiedContract := SourceUniform82427.uniform 14 (by decide)

def node047 : CertifiedContract := SourceStrictRunContracts82427.run 15 (by decide)

end
end JSP233.SourceNodes82427G2
