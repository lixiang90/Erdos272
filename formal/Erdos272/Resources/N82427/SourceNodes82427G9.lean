module

public import Erdos272.Arithmetic.N82427.CorrelatedChecks82427
public import Erdos272.Counting.N82427.CorrelatedChord82427
public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N82427.SourceNodes82427G8
public import Erdos272.Resources.N82427.SourceStrictRunContracts82427
public import Erdos272.Resources.N82427.SourceUniform82427

@[expose] public section

namespace JSP233.SourceNodes82427G9
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node144 : CertifiedContract where
  contract := ⟨132,11,46400⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=40) (by decide)
      hN hground hS hsize hdefect

def node145 : CertifiedContract where
  contract := ⟨392,1,46400⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=41) (by decide)
      hN hground hS hsize hdefect

def node146 : CertifiedContract where
  contract := ⟨88,49,50088⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=45) (by decide)
      hN hground hS hsize hdefect

def node147 : CertifiedContract where
  contract := ⟨132,12,50088⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=46) (by decide)
      hN hground hS hsize hdefect

def node148 : CertifiedContract where
  contract := ⟨407,1,50088⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=47) (by decide)
      hN hground hS hsize hdefect

def node149 : CertifiedContract where
  contract := ⟨88,51,52556⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=48) (by decide)
      hN hground hS hsize hdefect

def node150 : CertifiedContract where
  contract := ⟨132,13,52556⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=49) (by decide)
      hN hground hS hsize hdefect

def node151 : CertifiedContract where
  contract := ⟨418,1,52556⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=50) (by decide)
      hN hground hS hsize hdefect

def node152 : CertifiedContract where
  contract := ⟨88,53,54720⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=51) (by decide)
      hN hground hS hsize hdefect

def node153 : CertifiedContract where
  contract := ⟨132,14,54720⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=52) (by decide)
      hN hground hS hsize hdefect

def node154 : CertifiedContract where
  contract := ⟨426,1,54720⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=53) (by decide)
      hN hground hS hsize hdefect

def node155 : CertifiedContract where
  contract := ⟨88,55,57994⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=57) (by decide)
      hN hground hS hsize hdefect

def node156 : CertifiedContract where
  contract := ⟨132,15,57994⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=58) (by decide)
      hN hground hS hsize hdefect

def node157 : CertifiedContract where
  contract := ⟨439,1,57994⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas84364.actual_source (i:=59) (by decide)
      hN hground hS hsize hdefect

end
end JSP233.SourceNodes82427G9
