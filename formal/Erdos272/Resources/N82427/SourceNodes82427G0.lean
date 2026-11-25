module

public import Erdos272.Arithmetic.N82427.CorrelatedChecks82427
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N82427.SourceStrictRunContracts82427
public import Erdos272.Resources.N82427.SourceUniform82427

@[expose] public section

namespace JSP233.SourceNodes82427G0
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node000 : CertifiedContract := SourceUniform82427.uniform 0 (by decide)

def node001 : CertifiedContract := SourceStrictRunContracts82427.run 0 (by decide)

def node002 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan002)
    (CorrelatedChecks82427.checked002) SourceNodes82427G0.node001
    (by decide) (by decide) (by decide)

def node003 : CertifiedContract := SourceUniform82427.uniform 1 (by decide)

def node004 : CertifiedContract := SourceStrictRunContracts82427.run 1 (by decide)

def node005 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan005)
    (CorrelatedChecks82427.checked005) SourceNodes82427G0.node004
    (by decide) (by decide) (by decide)

def node006 : CertifiedContract := SourceUniform82427.uniform 2 (by decide)

def node007 : CertifiedContract := SourceStrictRunContracts82427.run 2 (by decide)

def node008 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan008)
    (CorrelatedChecks82427.checked008) SourceNodes82427G0.node007
    (by decide) (by decide) (by decide)

def node009 : CertifiedContract := SourceUniform82427.uniform 3 (by decide)

def node010 : CertifiedContract := SourceStrictRunContracts82427.run 3 (by decide)

def node011 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan011)
    (CorrelatedChecks82427.checked011) SourceNodes82427G0.node010
    (by decide) (by decide) (by decide)

def node012 : CertifiedContract := SourceUniform82427.uniform 4 (by decide)

def node013 : CertifiedContract := SourceStrictRunContracts82427.run 4 (by decide)

def node014 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan014)
    (CorrelatedChecks82427.checked014) SourceNodes82427G0.node013
    (by decide) (by decide) (by decide)

def node015 : CertifiedContract := SourceUniform82427.uniform 5 (by decide)

end
end JSP233.SourceNodes82427G0
