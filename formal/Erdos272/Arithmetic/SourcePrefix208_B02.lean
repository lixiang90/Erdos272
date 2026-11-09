module

public import Erdos272.Certificates.SourcePrefixBlocks208
public import Erdos272.Arithmetic.SourcePrefixSpecs208
public import Erdos272.Arithmetic.FastDecode208
public import Erdos272.Arithmetic.BatchSourceLinear208

@[expose] public section

/-! Exactly the actual physical sizes 2430..2685, target row 11.
The complete lookup has a separate kernel certificate. -/
set_option Elab.async false

namespace JSP233.SourcePrefix208_11_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2430 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2446 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2462 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2478 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2494 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2510 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2526 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2542 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2558 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2574 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2590 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2606 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2622 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2638 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2654 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2670 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 2430 2685
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 2430 2685
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_000


#check JSP233.SourcePrefix208_11_000.checked

/-! Exactly the actual physical sizes 2686..2941, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_001
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2686 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2702 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2718 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2734 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2750 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2766 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2782 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2798 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2814 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2830 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2846 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2862 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2878 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2894 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2910 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2926 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 2686 2941
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 2686 2941
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_001


#check JSP233.SourcePrefix208_11_001.checked

/-! Exactly the actual physical sizes 2942..3197, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_002
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2942 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2958 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2974 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2990 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3006 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3022 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3038 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3054 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3070 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3086 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3102 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3118 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3134 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3150 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3166 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3182 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 2942 3197
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 2942 3197
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_002


#check JSP233.SourcePrefix208_11_002.checked

/-! Exactly the actual physical sizes 3198..3453, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_003
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3198 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3214 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3230 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3246 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3262 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3278 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3294 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3310 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3326 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3342 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3358 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3374 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3390 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3406 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3422 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3438 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 3198 3453
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 3198 3453
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_003


#check JSP233.SourcePrefix208_11_003.checked

/-! Exactly the actual physical sizes 3454..3709, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_004
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3454 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3470 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3486 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3502 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3518 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3534 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3550 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3566 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3582 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3598 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3614 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3630 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3646 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3662 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3678 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3694 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 3454 3709
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 3454 3709
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_004


#check JSP233.SourcePrefix208_11_004.checked

/-! Exactly the actual physical sizes 3710..3965, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_005
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3710 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3726 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3742 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3758 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3774 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3790 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3806 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3822 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3838 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3854 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3870 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3886 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3902 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3918 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3934 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3950 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 3710 3965
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 3710 3965
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_005


#check JSP233.SourcePrefix208_11_005.checked

/-! Exactly the actual physical sizes 3966..4221, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_006
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3966 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3982 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 3998 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4014 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4030 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4046 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4062 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4078 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4094 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4110 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4126 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4142 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4158 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4174 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4190 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4206 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 3966 4221
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 3966 4221
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_006


#check JSP233.SourcePrefix208_11_006.checked

/-! Exactly the actual physical sizes 4222..4477, target row 11.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_11_007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4222 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4238 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4254 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4270 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4286 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4302 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4318 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4334 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4350 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4366 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4382 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4398 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4414 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4430 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4446 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 4462 16
      (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 4222 4477
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 4222 4477
    (SourcePrefixSpecs208.rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_11_007


#check JSP233.SourcePrefix208_11_007.checked
