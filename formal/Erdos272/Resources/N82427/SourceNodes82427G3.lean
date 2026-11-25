module

public import Erdos272.Arithmetic.N82427.CorrelatedChecks82427
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N82427.SourceNodes82427G2
public import Erdos272.Resources.N82427.SourceStrictRunContracts82427
public import Erdos272.Resources.N82427.SourceUniform82427

@[expose] public section

namespace JSP233.SourceNodes82427G3
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node048 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks82427.plan048)
    (CorrelatedChecks82427.checked048) SourceNodes82427G2.node044
    (by decide) (by decide) (by decide)

def node049 : CertifiedContract := SourceUniform82427.uniform 15 (by decide)

def node050 : CertifiedContract := SourceStrictRunContracts82427.run 16 (by decide)

def node051 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks82427.plan051)
    (CorrelatedChecks82427.checked051) SourceNodes82427G2.node044
    (by decide) (by decide) (by decide)

def node052 : CertifiedContract := SourceUniform82427.uniform 16 (by decide)

def node053 : CertifiedContract := SourceStrictRunContracts82427.run 17 (by decide)

def node054 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks82427.plan054)
    (CorrelatedChecks82427.checked054) SourceNodes82427G2.node044
    (by decide) (by decide) (by decide)

def node055 : CertifiedContract := SourceUniform82427.uniform 17 (by decide)

def node056 : CertifiedContract := SourceStrictRunContracts82427.run 18 (by decide)

def node057 : CertifiedContract where
  contract := ⟨130,19,68381⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=109) (by decide)
      hN hground hS hsize hdefect

def node058 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan058)
    (CorrelatedChecks82427.checked058) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node059 : CertifiedContract := SourceUniform82427.uniform 18 (by decide)

def node060 : CertifiedContract := SourceStrictRunContracts82427.run 19 (by decide)

def node061 : CertifiedContract where
  contract := ⟨132,9,39616⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=31) (by decide)
      hN hground hS hsize hdefect

def node062 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks82427.plan062)
    (CorrelatedChecks82427.checked062) SourceNodes82427G3.node061
    (by decide) (by decide) (by decide)

def node063 : CertifiedContract := SourceUniform82427.uniform 19 (by decide)

end
end JSP233.SourceNodes82427G3
