import Erdos272.Certificates.SourcePrefixLinear208
import Erdos272.Certificates.SourcePrefixBlocks208
import Erdos272.Arithmetic.SourcePrefixSpecs208
import Erdos272.Arithmetic.FastDecode208
import Erdos272.Arithmetic.BatchSourceLinear208

/-! Exactly the actual physical sizes 4478..4733, target row 11.
The complete lookup has a separate kernel certificate. -/
set_option Elab.async false

namespace JSP233.SourcePrefix208_11_008
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4478 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4494 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4510 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4526 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4542 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4558 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4574 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4590 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4606 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4622 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4638 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4654 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4670 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4686 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4702 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4718 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 4478 4733
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 4478 4733
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_008


#check JSP233.SourcePrefix208_11_008.checked

/-! Exactly the actual physical sizes 4734..4989, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_009
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4734 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4750 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4766 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4782 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4798 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4814 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4830 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4846 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4862 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4878 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4894 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4910 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4926 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4942 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4958 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4974 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 4734 4989
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 4734 4989
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_009


#check JSP233.SourcePrefix208_11_009.checked

/-! Exactly the actual physical sizes 4990..5245, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_010
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4990 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5006 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5022 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5038 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5054 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5070 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5086 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5102 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5118 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5134 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5150 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5166 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5182 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5198 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5214 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5230 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 4990 5245
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 4990 5245
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_010


#check JSP233.SourcePrefix208_11_010.checked

/-! Exactly the actual physical sizes 5246..5501, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_011
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5246 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5262 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5278 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5294 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5310 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5326 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5342 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5358 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5374 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5390 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5406 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5422 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5438 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5454 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5470 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5486 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 5246 5501
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 5246 5501
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_011


#check JSP233.SourcePrefix208_11_011.checked

/-! Exactly the actual physical sizes 5502..5757, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_012
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5502 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5518 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5534 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5550 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5566 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5582 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5598 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5614 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5630 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5646 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5662 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5678 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5694 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5710 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5726 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5742 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 5502 5757
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 5502 5757
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_012


#check JSP233.SourcePrefix208_11_012.checked

/-! Exactly the actual physical sizes 5758..6013, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_013
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5758 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5774 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5790 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5806 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5822 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5838 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5854 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5870 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5886 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5902 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5918 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5934 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5950 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5966 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5982 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 5998 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 5758 6013
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 5758 6013
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_013


#check JSP233.SourcePrefix208_11_013.checked

/-! Exactly the actual physical sizes 6014..6269, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_014
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6014 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6030 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6046 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6062 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6078 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6094 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6110 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6126 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6142 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6158 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6174 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6190 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6206 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6222 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6238 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6254 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 6014 6269
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 6014 6269
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_014


#check JSP233.SourcePrefix208_11_014.checked

/-! Exactly the actual physical sizes 6270..6525, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_015
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6270 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6286 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6302 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6318 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6334 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6350 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6366 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6382 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6398 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6414 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6430 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6446 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6462 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6478 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6494 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 6510 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  rw [BatchSource208.rowBlockCheck_eq_linear (by decide +kernel)]
  decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 6270 6525
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 6270 6525
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_015


#check JSP233.SourcePrefix208_11_015.checked
