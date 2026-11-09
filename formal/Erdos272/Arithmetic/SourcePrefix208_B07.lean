module

public import Erdos272.Certificates.SourcePrefixLinear208
public import Erdos272.Certificates.SourcePrefixBlocks208
public import Erdos272.Arithmetic.SourcePrefixSpecs208
public import Erdos272.Arithmetic.FastDecode208
public import Erdos272.Arithmetic.BatchSourceLinear208

@[expose] public section

/-! Exactly the actual physical sizes 12640..12895, target row 13.
The complete lookup has a separate kernel certificate. -/
set_option Elab.async false

namespace JSP233.SourcePrefix208_13_019
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12640 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12656 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12672 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12688 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12704 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12720 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12736 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12752 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12768 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12784 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12800 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12816 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12832 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12848 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12864 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12880 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 12640 12895
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 12640 12895
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_019


#check JSP233.SourcePrefix208_13_019.checked

/-! Exactly the actual physical sizes 12896..13151, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_020
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12896 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12912 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12928 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12944 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12960 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12976 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 12992 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13008 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13024 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13040 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13056 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13072 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13088 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13104 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13120 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13136 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 12896 13151
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 12896 13151
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_020


#check JSP233.SourcePrefix208_13_020.checked

/-! Exactly the actual physical sizes 13152..13407, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_021
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13152 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13168 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13184 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13200 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13216 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13232 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13248 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13264 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13280 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13296 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13312 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13328 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13344 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13360 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13376 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13392 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 13152 13407
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 13152 13407
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_021


#check JSP233.SourcePrefix208_13_021.checked

/-! Exactly the actual physical sizes 13408..13663, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_022
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13408 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13424 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13440 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13456 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13472 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13488 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13504 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13520 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13536 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13552 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13568 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13584 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13600 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13616 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13632 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13648 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 13408 13663
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 13408 13663
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_022


#check JSP233.SourcePrefix208_13_022.checked

/-! Exactly the actual physical sizes 13664..13919, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_023
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13664 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13680 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13696 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13712 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13728 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13744 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13760 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13776 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13792 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13808 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13824 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13840 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13856 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13872 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13888 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13904 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 13664 13919
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 13664 13919
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_023


#check JSP233.SourcePrefix208_13_023.checked

/-! Exactly the actual physical sizes 13920..14175, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_024
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13920 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13936 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13952 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13968 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 13984 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14000 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14016 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14032 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14048 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14064 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14080 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14096 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14112 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14128 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14144 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14160 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 13920 14175
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 13920 14175
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_024


#check JSP233.SourcePrefix208_13_024.checked

/-! Exactly the actual physical sizes 14176..14431, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_025
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14176 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14192 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14208 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14224 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14240 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14256 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14272 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14288 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14304 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14320 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14336 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14352 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14368 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14384 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14400 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14416 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 14176 14431
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 14176 14431
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_025


#check JSP233.SourcePrefix208_13_025.checked

/-! Exactly the actual physical sizes 14432..14687, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_026
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14432 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14448 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14464 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14480 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14496 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14512 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14528 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14544 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14560 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14576 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14592 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14608 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14624 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14640 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14656 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 14672 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 14432 14687
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 14432 14687
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_026


#check JSP233.SourcePrefix208_13_026.checked
