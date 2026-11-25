module

public import Erdos272.Arithmetic.N82427.CorrelatedChecks82427
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N82427.SourceNodes82427G6
public import Erdos272.Resources.N82427.SourceStrictRunContracts82427
public import Erdos272.Resources.N82427.SourceUniform82427

@[expose] public section

namespace JSP233.SourceNodes82427G7
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node112 : CertifiedContract := SourceStrictRunContracts82427.run 36 (by decide)

def node113 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan113)
    (CorrelatedChecks82427.checked113) SourceNodes82427G7.node112
    (by decide) (by decide) (by decide)

def node114 : CertifiedContract := SourceUniform82427.uniform 34 (by decide)

def node115 : CertifiedContract := SourceStrictRunContracts82427.run 37 (by decide)

def node116 : CertifiedContract :=
  SourceCorrelated86412.standard (CorrelatedChecks82427.plan116)
    (CorrelatedChecks82427.checked116) SourceNodes82427G3.node057
    (by decide) (by decide) (by decide)

def node117 : CertifiedContract := SourceUniform82427.uniform 35 (by decide)

def node118 : CertifiedContract where
  contract := ⟨88,1,2280⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=0) (by decide)
      hN hground hS hsize hdefect

def node119 : CertifiedContract where
  contract := ⟨88,6,11706⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=5) (by decide)
      hN hground hS hsize hdefect

def node120 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan120)
    (CorrelatedChecks82427.checked120) SourceNodes82427G7.node119
    (by decide) (by decide) (by decide)

def node121 : CertifiedContract := SourceUniform82427.uniform 36 (by decide)

def node122 : CertifiedContract where
  contract := ⟨88,10,17810⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=9) (by decide)
      hN hground hS hsize hdefect

def node123 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan123)
    (CorrelatedChecks82427.checked123) SourceNodes82427G7.node122
    (by decide) (by decide) (by decide)

def node124 : CertifiedContract := SourceUniform82427.uniform 37 (by decide)

def node125 : CertifiedContract where
  contract := ⟨88,14,22442⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=11) (by decide)
      hN hground hS hsize hdefect

def node126 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan126)
    (CorrelatedChecks82427.checked126) SourceNodes82427G7.node125
    (by decide) (by decide) (by decide)

def node127 : CertifiedContract := SourceUniform82427.uniform 38 (by decide)

end
end JSP233.SourceNodes82427G7
