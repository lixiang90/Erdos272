module

public import Erdos272.Arithmetic.N82427.CorrelatedChecks82427
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N86412.SourceAtlas86412
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N82427.SourceNodes82427G7
public import Erdos272.Resources.N82427.SourceStrictRunContracts82427
public import Erdos272.Resources.N82427.SourceUniform82427

@[expose] public section

namespace JSP233.SourceNodes82427G8
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node128 : CertifiedContract where
  contract := ⟨88,19,26106⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=15) (by decide)
      hN hground hS hsize hdefect

def node129 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan129)
    (CorrelatedChecks82427.checked129) SourceNodes82427G8.node128
    (by decide) (by decide) (by decide)

def node130 : CertifiedContract where
  contract := ⟨293,1,25823⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas86412.actual_source (i:=27) (by decide)
      hN hground hS hsize hdefect

def node131 : CertifiedContract where
  contract := ⟨88,25,28545⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=19) (by decide)
      hN hground hS hsize hdefect

def node132 : CertifiedContract :=
  CorrelatedChord82427.chord (CorrelatedChecks82427.plan132)
    (CorrelatedChecks82427.checked132) SourceNodes82427G8.node131
    (by decide) (by decide) (by decide)

def node133 : CertifiedContract := SourceUniform82427.uniform 39 (by decide)

def node134 : CertifiedContract where
  contract := ⟨88,37,33842⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=24) (by decide)
      hN hground hS hsize hdefect

def node135 : CertifiedContract where
  contract := ⟨335,1,33842⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=26) (by decide)
      hN hground hS hsize hdefect

def node136 : CertifiedContract where
  contract := ⟨88,39,36984⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=27) (by decide)
      hN hground hS hsize hdefect

def node137 : CertifiedContract where
  contract := ⟨154,6,36984⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=28) (by decide)
      hN hground hS hsize hdefect

def node138 : CertifiedContract where
  contract := ⟨351,1,36984⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=29) (by decide)
      hN hground hS hsize hdefect

def node139 : CertifiedContract where
  contract := ⟨88,41,39616⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=30) (by decide)
      hN hground hS hsize hdefect

def node140 : CertifiedContract where
  contract := ⟨363,1,39616⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=32) (by decide)
      hN hground hS hsize hdefect

def node141 : CertifiedContract where
  contract := ⟨88,43,42260⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=33) (by decide)
      hN hground hS hsize hdefect

def node142 : CertifiedContract where
  contract := ⟨132,10,42260⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=34) (by decide)
      hN hground hS hsize hdefect

def node143 : CertifiedContract where
  contract := ⟨88,46,46400⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=39) (by decide)
      hN hground hS hsize hdefect

end
end JSP233.SourceNodes82427G8
