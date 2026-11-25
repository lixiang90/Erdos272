module

public import Erdos272.Arithmetic.N82427.CorrelatedChecks82427
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N82427.SourceNodes82427G4
public import Erdos272.Resources.N82427.SourceStrictRunContracts82427
public import Erdos272.Resources.N82427.SourceUniform82427

@[expose] public section

namespace JSP233.SourceNodes82427G5
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node080 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks82427.plan080)
    (CorrelatedChecks82427.checked080) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node081 : CertifiedContract := SourceUniform82427.uniform 23 (by decide)

def node082 : CertifiedContract := SourceStrictRunContracts82427.run 26 (by decide)

def node083 : CertifiedContract :=
  SourceCorrelated86412.dynamic (CorrelatedChecks82427.plan083)
    (CorrelatedChecks82427.checked083) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node084 : CertifiedContract := SourceUniform82427.uniform 24 (by decide)

def node085 : CertifiedContract := SourceStrictRunContracts82427.run 27 (by decide)

def node086 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks82427.plan086)
    (CorrelatedChecks82427.checked086) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node087 : CertifiedContract := SourceUniform82427.uniform 25 (by decide)

def node088 : CertifiedContract := SourceStrictRunContracts82427.run 28 (by decide)

def node089 : CertifiedContract :=
  SourceCorrelated86412.dynamic (CorrelatedChecks82427.plan089)
    (CorrelatedChecks82427.checked089) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node090 : CertifiedContract := SourceUniform82427.uniform 26 (by decide)

def node091 : CertifiedContract := SourceStrictRunContracts82427.run 29 (by decide)

def node092 : CertifiedContract :=
  SourceCorrelated86412.dynamic (CorrelatedChecks82427.plan092)
    (CorrelatedChecks82427.checked092) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node093 : CertifiedContract := SourceUniform82427.uniform 27 (by decide)

def node094 : CertifiedContract := SourceStrictRunContracts82427.run 30 (by decide)

def node095 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks82427.plan095)
    (CorrelatedChecks82427.checked095) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

end
end JSP233.SourceNodes82427G5
