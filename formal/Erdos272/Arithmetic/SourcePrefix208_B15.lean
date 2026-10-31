import Erdos272.Certificates.SourcePrefixLinear208
import Erdos272.Certificates.SourcePrefixBlocks208
import Erdos272.Arithmetic.SourcePrefixSpecs208
import Erdos272.Arithmetic.FastDecode208
import Erdos272.Arithmetic.BatchSourceLinear208

/-! Exactly the actual physical sizes 29024..29279, target row 13.
The complete lookup has a separate kernel certificate. -/
set_option Elab.async false

namespace JSP233.SourcePrefix208_13_083
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29024 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29040 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29056 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29072 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29088 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29104 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29120 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29136 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29152 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29168 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29184 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29200 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29216 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29232 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29248 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29264 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 29024 29279
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 29024 29279
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_083


#check JSP233.SourcePrefix208_13_083.checked

/-! Exactly the actual physical sizes 29280..29535, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_084
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29280 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29296 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29312 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29328 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29344 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29360 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29376 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29392 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29408 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29424 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29440 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29456 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29472 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29488 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29504 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29520 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 29280 29535
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 29280 29535
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_084


#check JSP233.SourcePrefix208_13_084.checked

/-! Exactly the actual physical sizes 29536..29791, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_085
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29536 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29552 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29568 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29584 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29600 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29616 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29632 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29648 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29664 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29680 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29696 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29712 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29728 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29744 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29760 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29776 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 29536 29791
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 29536 29791
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_085


#check JSP233.SourcePrefix208_13_085.checked

/-! Exactly the actual physical sizes 29792..30047, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_086
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29792 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29808 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29824 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29840 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29856 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29872 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29888 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29904 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29920 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29936 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29952 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29968 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 29984 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30000 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30016 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30032 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 29792 30047
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 29792 30047
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_086


#check JSP233.SourcePrefix208_13_086.checked

/-! Exactly the actual physical sizes 30048..30303, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_087
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30048 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30064 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30080 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30096 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30112 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30128 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30144 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30160 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30176 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30192 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30208 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30224 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30240 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30256 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30272 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30288 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 30048 30303
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 30048 30303
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_087


#check JSP233.SourcePrefix208_13_087.checked

/-! Exactly the actual physical sizes 30304..30559, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_088
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30304 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30320 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30336 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30352 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30368 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30384 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30400 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30416 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30432 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30448 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30464 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30480 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30496 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30512 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30528 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30544 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 30304 30559
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 30304 30559
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_088


#check JSP233.SourcePrefix208_13_088.checked

/-! Exactly the actual physical sizes 30560..30815, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_089
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30560 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30576 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30592 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30608 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30624 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30640 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30656 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30672 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30688 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30704 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30720 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30736 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30752 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30768 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30784 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30800 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 30560 30815
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 30560 30815
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_089


#check JSP233.SourcePrefix208_13_089.checked

/-! Exactly the actual physical sizes 30816..31071, target row 13.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_13_090
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30816 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30832 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30848 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30864 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30880 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30896 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30912 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30928 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30944 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30960 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30976 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 30992 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 31008 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 31024 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 31040 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 31056 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 30816 31071
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 30816 31071
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_090


#check JSP233.SourcePrefix208_13_090.checked
