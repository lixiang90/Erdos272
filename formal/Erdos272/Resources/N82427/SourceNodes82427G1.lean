module

public import Erdos272.Arithmetic.N82427.CorrelatedChecks82427
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N82427.SourceNodes82427G0
public import Erdos272.Resources.N82427.SourceStrictRunContracts82427
public import Erdos272.Resources.N82427.SourceUniform82427

@[expose] public section

namespace JSP233.SourceNodes82427G1
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node016 : CertifiedContract := SourceStrictRunContracts82427.run 5 (by decide)

def node017 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan017)
    (CorrelatedChecks82427.checked017) SourceNodes82427G1.node016
    (by decide) (by decide) (by decide)

def node018 : CertifiedContract := SourceUniform82427.uniform 6 (by decide)

def node019 : CertifiedContract := SourceStrictRunContracts82427.run 6 (by decide)

def node020 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan020)
    (CorrelatedChecks82427.checked020) SourceNodes82427G1.node019
    (by decide) (by decide) (by decide)

def node021 : CertifiedContract := SourceUniform82427.uniform 7 (by decide)

def node022 : CertifiedContract := SourceStrictRunContracts82427.run 7 (by decide)

def node023 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan023)
    (CorrelatedChecks82427.checked023) SourceNodes82427G1.node022
    (by decide) (by decide) (by decide)

def node024 : CertifiedContract := SourceUniform82427.uniform 8 (by decide)

def node025 : CertifiedContract := SourceStrictRunContracts82427.run 8 (by decide)

def node026 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan026)
    (CorrelatedChecks82427.checked026) SourceNodes82427G1.node025
    (by decide) (by decide) (by decide)

def node027 : CertifiedContract := SourceUniform82427.uniform 9 (by decide)

def node028 : CertifiedContract := SourceStrictRunContracts82427.run 9 (by decide)

def node029 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan029)
    (CorrelatedChecks82427.checked029) SourceNodes82427G1.node028
    (by decide) (by decide) (by decide)

def node030 : CertifiedContract := SourceUniform82427.uniform 10 (by decide)

def node031 : CertifiedContract := SourceStrictRunContracts82427.run 10 (by decide)

end
end JSP233.SourceNodes82427G1
