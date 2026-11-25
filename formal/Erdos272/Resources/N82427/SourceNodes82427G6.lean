module

public import Erdos272.Arithmetic.N82427.CorrelatedChecks82427
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N82427.SourceNodes82427G5
public import Erdos272.Resources.N82427.SourceStrictRunContracts82427
public import Erdos272.Resources.N82427.SourceUniform82427

@[expose] public section

namespace JSP233.SourceNodes82427G6
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node096 : CertifiedContract := SourceUniform82427.uniform 28 (by decide)

def node097 : CertifiedContract := SourceStrictRunContracts82427.run 31 (by decide)

def node098 : CertifiedContract :=
  SourceCorrelated86412.dynamic (CorrelatedChecks82427.plan098)
    (CorrelatedChecks82427.checked098) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node099 : CertifiedContract := SourceUniform82427.uniform 29 (by decide)

def node100 : CertifiedContract := SourceStrictRunContracts82427.run 32 (by decide)

def node101 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks82427.plan101)
    (CorrelatedChecks82427.checked101) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node102 : CertifiedContract := SourceUniform82427.uniform 30 (by decide)

def node103 : CertifiedContract := SourceStrictRunContracts82427.run 33 (by decide)

def node104 : CertifiedContract :=
  SourceCorrelated86412.dynamic (CorrelatedChecks82427.plan104)
    (CorrelatedChecks82427.checked104) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node105 : CertifiedContract := SourceUniform82427.uniform 31 (by decide)

def node106 : CertifiedContract := SourceStrictRunContracts82427.run 34 (by decide)

def node107 : CertifiedContract :=
  SourceCorrelated86412.dynamic (CorrelatedChecks82427.plan107)
    (CorrelatedChecks82427.checked107) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node108 : CertifiedContract := SourceUniform82427.uniform 32 (by decide)

def node109 : CertifiedContract := SourceStrictRunContracts82427.run 35 (by decide)

def node110 : CertifiedContract :=
  SourceCorrelated86412.dynamic (CorrelatedChecks82427.plan110)
    (CorrelatedChecks82427.checked110) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node111 : CertifiedContract := SourceUniform82427.uniform 33 (by decide)

end
end JSP233.SourceNodes82427G6
