module

public import Erdos272.Certificates.SourcePrefixLinear208
public import Erdos272.Certificates.SourcePrefixBlocks208
public import Erdos272.Arithmetic.SourcePrefixSpecs208
public import Erdos272.Arithmetic.FastDecode208
public import Erdos272.Arithmetic.BatchSourceLinear208

@[expose] public section

/-! Exactly the actual physical sizes 10592..10847, target row 13.
The complete lookup has a separate kernel certificate. -/
set_option Elab.async false

namespace JSP233.SourcePrefix208_13_011
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10592 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10608 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10624 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10640 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10656 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10672 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10688 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10704 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10720 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10736 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10752 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10768 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10784 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10800 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10816 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10832 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 10592 10847
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 16)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000
  · exact checkedPart001
  · exact checkedPart002
  · exact checkedPart003
  · exact checkedPart004
  · exact checkedPart005
  · exact checkedPart006
  · exact checkedPart007
  · exact checkedPart008
  · exact checkedPart009
  · exact checkedPart010
  · exact checkedPart011
  · exact checkedPart012
  · exact checkedPart013
  · exact checkedPart014
  · exact checkedPart015

theorem checked : BatchSource208.checkBlock FastDecode208.phi 10592 10847
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_011


#check JSP233.SourcePrefix208_13_011.checked

/-! Exactly the actual physical sizes 10848..11103, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_012
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10848 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10864 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10880 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10896 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10912 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10928 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10944 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10960 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10976 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 10992 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11008 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11024 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11040 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11056 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11072 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11088 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 10848 11103
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 16)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000
  · exact checkedPart001
  · exact checkedPart002
  · exact checkedPart003
  · exact checkedPart004
  · exact checkedPart005
  · exact checkedPart006
  · exact checkedPart007
  · exact checkedPart008
  · exact checkedPart009
  · exact checkedPart010
  · exact checkedPart011
  · exact checkedPart012
  · exact checkedPart013
  · exact checkedPart014
  · exact checkedPart015

theorem checked : BatchSource208.checkBlock FastDecode208.phi 10848 11103
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_012


#check JSP233.SourcePrefix208_13_012.checked

/-! Exactly the actual physical sizes 11104..11359, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_013
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11104 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11120 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11136 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11152 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11168 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11184 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11200 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11216 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11232 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11248 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11264 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11280 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11296 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11312 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11328 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11344 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 11104 11359
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 16)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000
  · exact checkedPart001
  · exact checkedPart002
  · exact checkedPart003
  · exact checkedPart004
  · exact checkedPart005
  · exact checkedPart006
  · exact checkedPart007
  · exact checkedPart008
  · exact checkedPart009
  · exact checkedPart010
  · exact checkedPart011
  · exact checkedPart012
  · exact checkedPart013
  · exact checkedPart014
  · exact checkedPart015

theorem checked : BatchSource208.checkBlock FastDecode208.phi 11104 11359
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_013


#check JSP233.SourcePrefix208_13_013.checked

/-! Exactly the actual physical sizes 11360..11615, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_014
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11360 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11376 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11392 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11408 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11424 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11440 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11456 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11472 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11488 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11504 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11520 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11536 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11552 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11568 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11584 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11600 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 11360 11615
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 16)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000
  · exact checkedPart001
  · exact checkedPart002
  · exact checkedPart003
  · exact checkedPart004
  · exact checkedPart005
  · exact checkedPart006
  · exact checkedPart007
  · exact checkedPart008
  · exact checkedPart009
  · exact checkedPart010
  · exact checkedPart011
  · exact checkedPart012
  · exact checkedPart013
  · exact checkedPart014
  · exact checkedPart015

theorem checked : BatchSource208.checkBlock FastDecode208.phi 11360 11615
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_014


#check JSP233.SourcePrefix208_13_014.checked

/-! Exactly the actual physical sizes 11616..11871, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_015
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11616 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11632 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11648 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11664 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11680 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11696 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11712 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11728 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11744 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11760 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11776 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11792 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11808 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11824 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11840 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11856 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 11616 11871
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 16)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000
  · exact checkedPart001
  · exact checkedPart002
  · exact checkedPart003
  · exact checkedPart004
  · exact checkedPart005
  · exact checkedPart006
  · exact checkedPart007
  · exact checkedPart008
  · exact checkedPart009
  · exact checkedPart010
  · exact checkedPart011
  · exact checkedPart012
  · exact checkedPart013
  · exact checkedPart014
  · exact checkedPart015

theorem checked : BatchSource208.checkBlock FastDecode208.phi 11616 11871
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_015


#check JSP233.SourcePrefix208_13_015.checked

/-! Exactly the actual physical sizes 11872..12127, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_016
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11872 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11888 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11904 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11920 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11936 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11952 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11968 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 11984 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12000 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12016 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12032 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12048 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12064 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12080 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12096 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12112 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 11872 12127
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 16)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000
  · exact checkedPart001
  · exact checkedPart002
  · exact checkedPart003
  · exact checkedPart004
  · exact checkedPart005
  · exact checkedPart006
  · exact checkedPart007
  · exact checkedPart008
  · exact checkedPart009
  · exact checkedPart010
  · exact checkedPart011
  · exact checkedPart012
  · exact checkedPart013
  · exact checkedPart014
  · exact checkedPart015

theorem checked : BatchSource208.checkBlock FastDecode208.phi 11872 12127
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_016


#check JSP233.SourcePrefix208_13_016.checked

/-! Exactly the actual physical sizes 12128..12383, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_017
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12128 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12144 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12160 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12176 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12192 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12208 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12224 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12240 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12256 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12272 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12288 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12304 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12320 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12336 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12352 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12368 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 12128 12383
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 16)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000
  · exact checkedPart001
  · exact checkedPart002
  · exact checkedPart003
  · exact checkedPart004
  · exact checkedPart005
  · exact checkedPart006
  · exact checkedPart007
  · exact checkedPart008
  · exact checkedPart009
  · exact checkedPart010
  · exact checkedPart011
  · exact checkedPart012
  · exact checkedPart013
  · exact checkedPart014
  · exact checkedPart015

theorem checked : BatchSource208.checkBlock FastDecode208.phi 12128 12383
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_017


#check JSP233.SourcePrefix208_13_017.checked

/-! Exactly the actual physical sizes 12384..12639, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_018
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12384 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12400 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12416 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12432 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12448 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12464 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12480 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12496 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12512 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12528 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12544 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12560 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12576 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12592 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12608 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12624 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 12384 12639
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 16)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000
  · exact checkedPart001
  · exact checkedPart002
  · exact checkedPart003
  · exact checkedPart004
  · exact checkedPart005
  · exact checkedPart006
  · exact checkedPart007
  · exact checkedPart008
  · exact checkedPart009
  · exact checkedPart010
  · exact checkedPart011
  · exact checkedPart012
  · exact checkedPart013
  · exact checkedPart014
  · exact checkedPart015

theorem checked : BatchSource208.checkBlock FastDecode208.phi 12384 12639
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_018


#check JSP233.SourcePrefix208_13_018.checked
