module

public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N142758.RowSources142758
public import Erdos272.Resources.N150465.RowSources150465
public import Erdos272.Resources.N158375.RowSources158375
public import Erdos272.Resources.N88404.SourceAtlas88404

@[expose] public section

namespace JSP233.SourceOld86412
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def old00 : CertifiedContract where
  contract := ⟨(SourceQueryData142758.query 9).lower,(SourceQueryData142758.query 9).defect,(SourceQueryData142758.query 9).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact CorrelatedSource158375.actual_plan_source (SourceQueryData142758.query 9)
      (SourceQueryData142758.conditions (by decide)) (RowSources142758.floors (by decide))
      hN hground hS hsize hdefect

def old01 : CertifiedContract where
  contract := ⟨(SourceQueryData150465.query 2).lower,(SourceQueryData150465.query 2).defect,(SourceQueryData150465.query 2).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact CorrelatedSource158375.actual_plan_source (SourceQueryData150465.query 2)
      (SourceQueryData150465.conditions (by decide)) (RowSources150465.floors (by decide))
      hN hground hS hsize hdefect

def old02 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 22).lower,(SourceAtlas88404.demand 22).defect,(SourceAtlas88404.demand 22).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 22) (by decide)
      hN hground hS hsize hdefect

def old03 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 28).lower,(SourceAtlas88404.demand 28).defect,(SourceAtlas88404.demand 28).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 28) (by decide)
      hN hground hS hsize hdefect

def old04 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 34).lower,(SourceAtlas88404.demand 34).defect,(SourceAtlas88404.demand 34).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 34) (by decide)
      hN hground hS hsize hdefect

def old05 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 43).lower,(SourceAtlas88404.demand 43).defect,(SourceAtlas88404.demand 43).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 43) (by decide)
      hN hground hS hsize hdefect

def old06 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 49).lower,(SourceAtlas88404.demand 49).defect,(SourceAtlas88404.demand 49).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 49) (by decide)
      hN hground hS hsize hdefect

def old07 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 55).lower,(SourceAtlas88404.demand 55).defect,(SourceAtlas88404.demand 55).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 55) (by decide)
      hN hground hS hsize hdefect

def old08 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 64).lower,(SourceAtlas88404.demand 64).defect,(SourceAtlas88404.demand 64).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 64) (by decide)
      hN hground hS hsize hdefect

def old09 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 83).lower,(SourceAtlas88404.demand 83).defect,(SourceAtlas88404.demand 83).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 83) (by decide)
      hN hground hS hsize hdefect

def old10 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 143).lower,(SourceAtlas88404.demand 143).defect,(SourceAtlas88404.demand 143).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 143) (by decide)
      hN hground hS hsize hdefect

def old11 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 243).lower,(SourceAtlas88404.demand 243).defect,(SourceAtlas88404.demand 243).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 243) (by decide)
      hN hground hS hsize hdefect

def old12 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 147).lower,(SourceAtlas88404.demand 147).defect,(SourceAtlas88404.demand 147).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 147) (by decide)
      hN hground hS hsize hdefect

def old13 : CertifiedContract where
  contract := ⟨(SourceQueryData142758.query 159).lower,(SourceQueryData142758.query 159).defect,(SourceQueryData142758.query 159).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact CorrelatedSource158375.actual_plan_source (SourceQueryData142758.query 159)
      (SourceQueryData142758.conditions (by decide)) (RowSources142758.floors (by decide))
      hN hground hS hsize hdefect

def old14 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 7).lower,(SourceAtlas88404.demand 7).defect,(SourceAtlas88404.demand 7).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 7) (by decide)
      hN hground hS hsize hdefect

def old15 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 25).lower,(SourceAtlas88404.demand 25).defect,(SourceAtlas88404.demand 25).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 25) (by decide)
      hN hground hS hsize hdefect

def old16 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 26).lower,(SourceAtlas88404.demand 26).defect,(SourceAtlas88404.demand 26).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 26) (by decide)
      hN hground hS hsize hdefect

def old17 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 50).lower,(SourceAtlas88404.demand 50).defect,(SourceAtlas88404.demand 50).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 50) (by decide)
      hN hground hS hsize hdefect

def old18 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 85).lower,(SourceAtlas88404.demand 85).defect,(SourceAtlas88404.demand 85).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 85) (by decide)
      hN hground hS hsize hdefect

def old19 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 86).lower,(SourceAtlas88404.demand 86).defect,(SourceAtlas88404.demand 86).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 86) (by decide)
      hN hground hS hsize hdefect

def old20 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 91).lower,(SourceAtlas88404.demand 91).defect,(SourceAtlas88404.demand 91).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 91) (by decide)
      hN hground hS hsize hdefect

def old21 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 92).lower,(SourceAtlas88404.demand 92).defect,(SourceAtlas88404.demand 92).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 92) (by decide)
      hN hground hS hsize hdefect

def old22 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 103).lower,(SourceAtlas88404.demand 103).defect,(SourceAtlas88404.demand 103).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 103) (by decide)
      hN hground hS hsize hdefect

def old23 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 104).lower,(SourceAtlas88404.demand 104).defect,(SourceAtlas88404.demand 104).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 104) (by decide)
      hN hground hS hsize hdefect

def old24 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 112).lower,(SourceAtlas88404.demand 112).defect,(SourceAtlas88404.demand 112).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 112) (by decide)
      hN hground hS hsize hdefect

def old25 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 113).lower,(SourceAtlas88404.demand 113).defect,(SourceAtlas88404.demand 113).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 113) (by decide)
      hN hground hS hsize hdefect

def old26 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 121).lower,(SourceAtlas88404.demand 121).defect,(SourceAtlas88404.demand 121).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 121) (by decide)
      hN hground hS hsize hdefect

def old27 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 122).lower,(SourceAtlas88404.demand 122).defect,(SourceAtlas88404.demand 122).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 122) (by decide)
      hN hground hS hsize hdefect

def old28 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 127).lower,(SourceAtlas88404.demand 127).defect,(SourceAtlas88404.demand 127).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 127) (by decide)
      hN hground hS hsize hdefect

def old29 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 128).lower,(SourceAtlas88404.demand 128).defect,(SourceAtlas88404.demand 128).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 128) (by decide)
      hN hground hS hsize hdefect

def old30 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 133).lower,(SourceAtlas88404.demand 133).defect,(SourceAtlas88404.demand 133).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 133) (by decide)
      hN hground hS hsize hdefect

def old31 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 134).lower,(SourceAtlas88404.demand 134).defect,(SourceAtlas88404.demand 134).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 134) (by decide)
      hN hground hS hsize hdefect

def old32 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 139).lower,(SourceAtlas88404.demand 139).defect,(SourceAtlas88404.demand 139).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 139) (by decide)
      hN hground hS hsize hdefect

def old33 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 140).lower,(SourceAtlas88404.demand 140).defect,(SourceAtlas88404.demand 140).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 140) (by decide)
      hN hground hS hsize hdefect

def old34 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 146).lower,(SourceAtlas88404.demand 146).defect,(SourceAtlas88404.demand 146).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 146) (by decide)
      hN hground hS hsize hdefect

def old35 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 246).lower,(SourceAtlas88404.demand 246).defect,(SourceAtlas88404.demand 246).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 246) (by decide)
      hN hground hS hsize hdefect

def old36 : CertifiedContract where
  contract := ⟨(SourceAtlas88404.demand 247).lower,(SourceAtlas88404.demand 247).defect,(SourceAtlas88404.demand 247).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas88404.actual_source (i := 247) (by decide)
      hN hground hS hsize hdefect

def old37 : CertifiedContract where
  contract := ⟨(SourceQueryData158375.query 81).lower,(SourceQueryData158375.query 81).defect,(SourceQueryData158375.query 81).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact CorrelatedSource158375.actual_plan_source (SourceQueryData158375.query 81)
      (SourceQueryData158375.conditions (by decide)) (RowSources158375.floors (by decide))
      hN hground hS hsize hdefect

def old (i : ℕ) : CertifiedContract :=
  match i with
  | 0 => old00
  | 1 => old01
  | 2 => old02
  | 3 => old03
  | 4 => old04
  | 5 => old05
  | 6 => old06
  | 7 => old07
  | 8 => old08
  | 9 => old09
  | 10 => old10
  | 11 => old11
  | 12 => old12
  | 13 => old13
  | 14 => old14
  | 15 => old15
  | 16 => old16
  | 17 => old17
  | 18 => old18
  | 19 => old19
  | 20 => old20
  | 21 => old21
  | 22 => old22
  | 23 => old23
  | 24 => old24
  | 25 => old25
  | 26 => old26
  | 27 => old27
  | 28 => old28
  | 29 => old29
  | 30 => old30
  | 31 => old31
  | 32 => old32
  | 33 => old33
  | 34 => old34
  | 35 => old35
  | 36 => old36
  | 37 => old37
  | _ => old00

end
end JSP233.SourceOld86412
