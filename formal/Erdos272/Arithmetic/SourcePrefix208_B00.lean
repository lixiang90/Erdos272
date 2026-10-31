import Erdos272.Certificates.SourcePrefixBlocks208
import Erdos272.Arithmetic.SourcePrefixSpecs208
import Erdos272.Arithmetic.FastDecode208
import Erdos272.Arithmetic.BatchSourceLinear208

/-! Exactly the actual physical sizes 242..242, target row 0.
The complete lookup has a separate kernel certificate. -/
set_option Elab.async false

namespace JSP233.SourcePrefix208_00_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 242 1
      (SourcePrefixSpecs208.rowTargets (⟨0, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 242 242
    (SourcePrefixSpecs208.rowTargets (⟨0, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 1)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000

theorem checked : BatchSource208.checkBlock FastDecode208.phi 242 242
    (SourcePrefixSpecs208.rowTargets (⟨0, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_00_000


#check JSP233.SourcePrefix208_00_000.checked

/-! Exactly the actual physical sizes 243..337, target row 1.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_01_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 243 16
      (SourcePrefixSpecs208.rowTargets (⟨1, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 259 16
      (SourcePrefixSpecs208.rowTargets (⟨1, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 275 16
      (SourcePrefixSpecs208.rowTargets (⟨1, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 291 16
      (SourcePrefixSpecs208.rowTargets (⟨1, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 307 16
      (SourcePrefixSpecs208.rowTargets (⟨1, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 323 15
      (SourcePrefixSpecs208.rowTargets (⟨1, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 243 337
    (SourcePrefixSpecs208.rowTargets (⟨1, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 6)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000
  · exact checkedPart001
  · exact checkedPart002
  · exact checkedPart003
  · exact checkedPart004
  · exact checkedPart005

theorem checked : BatchSource208.checkBlock FastDecode208.phi 243 337
    (SourcePrefixSpecs208.rowTargets (⟨1, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_01_000


#check JSP233.SourcePrefix208_01_000.checked

/-! Exactly the actual physical sizes 338..339, target row 2.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_02_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 338 2
      (SourcePrefixSpecs208.rowTargets (⟨2, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 338 339
    (SourcePrefixSpecs208.rowTargets (⟨2, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 1)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000

theorem checked : BatchSource208.checkBlock FastDecode208.phi 338 339
    (SourcePrefixSpecs208.rowTargets (⟨2, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_02_000


#check JSP233.SourcePrefix208_02_000.checked

/-! Exactly the actual physical sizes 340..483, target row 3.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_03_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 340 16
      (SourcePrefixSpecs208.rowTargets (⟨3, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 356 16
      (SourcePrefixSpecs208.rowTargets (⟨3, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 372 16
      (SourcePrefixSpecs208.rowTargets (⟨3, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 388 16
      (SourcePrefixSpecs208.rowTargets (⟨3, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 404 16
      (SourcePrefixSpecs208.rowTargets (⟨3, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 420 16
      (SourcePrefixSpecs208.rowTargets (⟨3, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 436 16
      (SourcePrefixSpecs208.rowTargets (⟨3, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 452 16
      (SourcePrefixSpecs208.rowTargets (⟨3, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 468 16
      (SourcePrefixSpecs208.rowTargets (⟨3, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 340 483
    (SourcePrefixSpecs208.rowTargets (⟨3, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 9)
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 340 483
    (SourcePrefixSpecs208.rowTargets (⟨3, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_03_000


#check JSP233.SourcePrefix208_03_000.checked

/-! Exactly the actual physical sizes 484..485, target row 4.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_04_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 484 2
      (SourcePrefixSpecs208.rowTargets (⟨4, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 484 485
    (SourcePrefixSpecs208.rowTargets (⟨4, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 1)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000

theorem checked : BatchSource208.checkBlock FastDecode208.phi 484 485
    (SourcePrefixSpecs208.rowTargets (⟨4, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_04_000


#check JSP233.SourcePrefix208_04_000.checked

/-! Exactly the actual physical sizes 486..725, target row 5.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_05_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 486 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 502 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 518 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 534 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 550 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 566 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 582 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 598 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 614 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 630 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 646 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 662 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 678 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 694 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 710 16
      (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 486 725
    (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 15)
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 486 725
    (SourcePrefixSpecs208.rowTargets (⟨5, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_05_000


#check JSP233.SourcePrefix208_05_000.checked

/-! Exactly the actual physical sizes 726..728, target row 6.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_06_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 726 3
      (SourcePrefixSpecs208.rowTargets (⟨6, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 726 728
    (SourcePrefixSpecs208.rowTargets (⟨6, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 1)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000

theorem checked : BatchSource208.checkBlock FastDecode208.phi 726 728
    (SourcePrefixSpecs208.rowTargets (⟨6, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_06_000


#check JSP233.SourcePrefix208_06_000.checked

/-! Exactly the actual physical sizes 729..984, target row 7.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_07_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 729 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 745 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 761 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 777 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 793 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 809 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 825 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 841 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 857 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 873 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 889 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 905 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 921 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 937 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 953 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 969 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 729 984
    (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 729 984
    (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_07_000


#check JSP233.SourcePrefix208_07_000.checked
