import Erdos272.Certificates.SourcePrefixLinear208
import Erdos272.Certificates.SourcePrefixBlocks208
import Erdos272.Arithmetic.SourcePrefixSpecs208
import Erdos272.Arithmetic.FastDecode208
import Erdos272.Arithmetic.BatchSourceLinear208

/-! Exactly the actual physical sizes 16736..16991, target row 13.
The complete lookup has a separate kernel certificate. -/
set_option Elab.async false

namespace JSP233.SourcePrefix208_13_035
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16736 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16752 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16768 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16784 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16800 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16816 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16832 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16848 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16864 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16880 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16896 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16912 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16928 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16944 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16960 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16976 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 16736 16991
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 16736 16991
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_035


#check JSP233.SourcePrefix208_13_035.checked

/-! Exactly the actual physical sizes 16992..17247, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_036
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 16992 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17008 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17024 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17040 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17056 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17072 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17088 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17104 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17120 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17136 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17152 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17168 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17184 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17200 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17216 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17232 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 16992 17247
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 16992 17247
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_036


#check JSP233.SourcePrefix208_13_036.checked

/-! Exactly the actual physical sizes 17248..17503, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_037
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17248 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17264 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17280 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17296 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17312 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17328 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17344 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17360 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17376 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17392 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17408 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17424 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17440 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17456 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17472 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17488 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 17248 17503
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 17248 17503
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_037


#check JSP233.SourcePrefix208_13_037.checked

/-! Exactly the actual physical sizes 17504..17759, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_038
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17504 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17520 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17536 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17552 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17568 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17584 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17600 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17616 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17632 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17648 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17664 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17680 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17696 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17712 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17728 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17744 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 17504 17759
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 17504 17759
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_038


#check JSP233.SourcePrefix208_13_038.checked

/-! Exactly the actual physical sizes 17760..18015, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_039
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17760 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17776 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17792 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17808 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17824 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17840 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17856 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17872 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17888 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17904 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17920 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17936 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17952 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17968 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 17984 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18000 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 17760 18015
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 17760 18015
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_039


#check JSP233.SourcePrefix208_13_039.checked

/-! Exactly the actual physical sizes 18016..18271, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_040
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18016 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18032 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18048 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18064 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18080 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18096 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18112 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18128 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18144 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18160 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18176 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18192 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18208 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18224 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18240 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18256 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 18016 18271
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 18016 18271
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_040


#check JSP233.SourcePrefix208_13_040.checked

/-! Exactly the actual physical sizes 18272..18527, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_041
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18272 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18288 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18304 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18320 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18336 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18352 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18368 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18384 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18400 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18416 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18432 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18448 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18464 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18480 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18496 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18512 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 18272 18527
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 18272 18527
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_041


#check JSP233.SourcePrefix208_13_041.checked

/-! Exactly the actual physical sizes 18528..18783, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_042
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18528 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18544 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18560 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18576 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18592 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18608 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18624 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18640 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18656 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18672 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18688 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18704 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18720 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18736 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18752 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 18768 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 18528 18783
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 18528 18783
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_042


#check JSP233.SourcePrefix208_13_042.checked
