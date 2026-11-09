module

public import Erdos272.Certificates.SourcePrefixBlocks208
public import Erdos272.Arithmetic.SourcePrefixSpecs208
public import Erdos272.Arithmetic.FastDecode208
public import Erdos272.Arithmetic.BatchSourceLinear208

@[expose] public section

/-! Exactly the actual physical sizes 7776..8031, target row 13.
The complete lookup has a separate kernel certificate. -/
set_option Elab.async false

namespace JSP233.SourcePrefix208_13_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7776 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7792 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7808 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7824 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7840 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7856 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7872 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7888 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7904 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7920 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7936 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7952 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7968 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 7984 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 8000 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 8016 16
      (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 7776 8031
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 7776 8031
    (SourcePrefixSpecs208.rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_13_000
