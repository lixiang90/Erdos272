module

public import Erdos272.Certificates.SourcePrefixBlocks208
public import Erdos272.Arithmetic.SourcePrefixSpecs208
public import Erdos272.Arithmetic.FastDecode208
public import Erdos272.Arithmetic.BatchSourceLinear208

@[expose] public section

/-! Exactly the actual physical sizes 985..1209, target row 7.
The complete lookup has a separate kernel certificate. -/
set_option Elab.async false

namespace JSP233.SourcePrefix208_07_001
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 985 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1001 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1017 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1033 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1049 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1065 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1081 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1097 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1113 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1129 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1145 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1161 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1177 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1193 16
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1209 1
      (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 985 1209
    (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 985 1209
    (SourcePrefixSpecs208.rowTargets (⟨7, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_07_001


#check JSP233.SourcePrefix208_07_001.checked

/-! Exactly the actual physical sizes 1210..1214, target row 8.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_08_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1210 5
      (SourcePrefixSpecs208.rowTargets (⟨8, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 1210 1214
    (SourcePrefixSpecs208.rowTargets (⟨8, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 1)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000

theorem checked : BatchSource208.checkBlock FastDecode208.phi 1210 1214
    (SourcePrefixSpecs208.rowTargets (⟨8, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_08_000


#check JSP233.SourcePrefix208_08_000.checked

/-! Exactly the actual physical sizes 1215..1470, target row 9.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_09_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1215 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1231 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1247 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1263 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1279 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1295 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1311 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1327 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1343 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1359 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1375 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1391 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1407 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1423 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1439 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1455 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 1215 1470
    (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 1215 1470
    (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_09_000


#check JSP233.SourcePrefix208_09_000.checked

/-! Exactly the actual physical sizes 1471..1726, target row 9.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_09_001
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1471 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1487 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1503 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1519 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1535 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1551 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1567 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1583 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1599 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1615 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1631 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1647 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1663 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1679 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1695 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1711 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 1471 1726
    (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 1471 1726
    (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_09_001


#check JSP233.SourcePrefix208_09_001.checked

/-! Exactly the actual physical sizes 1727..1982, target row 9.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_09_002
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1727 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1743 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1759 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1775 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1791 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1807 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1823 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1839 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1855 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1871 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1887 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1903 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1919 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1935 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1951 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1967 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 1727 1982
    (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 1727 1982
    (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_09_002


#check JSP233.SourcePrefix208_09_002.checked

/-! Exactly the actual physical sizes 1983..2238, target row 9.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_09_003
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1983 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 1999 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2015 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2031 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2047 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2063 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2079 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2095 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2111 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2127 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2143 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2159 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart012 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2175 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart013 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2191 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart014 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2207 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart015 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2223 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 1983 2238
    (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 1983 2238
    (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_09_003


#check JSP233.SourcePrefix208_09_003.checked

/-! Exactly the actual physical sizes 2239..2419, target row 9.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_09_004
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2239 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart001 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2255 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart002 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2271 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart003 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2287 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart004 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2303 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart005 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2319 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart006 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2335 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart007 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2351 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart008 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2367 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart009 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2383 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart010 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2399 16
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

private theorem checkedPart011 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2415 5
      (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 2239 2419
    (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 12)
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

theorem checked : BatchSource208.checkBlock FastDecode208.phi 2239 2419
    (SourcePrefixSpecs208.rowTargets (⟨9, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_09_004


#check JSP233.SourcePrefix208_09_004.checked

/-! Exactly the actual physical sizes 2420..2429, target row 10.
The complete lookup has a separate kernel certificate. -/
namespace JSP233.SourcePrefix208_10_000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem checkedPart000 :
    BatchSource208.rowBlockCheck FastDecode208.phi 2420 10
      (SourcePrefixSpecs208.rowTargets (⟨10, by decide⟩ : Fin 14)) = true := by decide +kernel

theorem checked_linear : BatchSourceLinear208.checkBlock FastDecode208.phi 2420 2429
    (SourcePrefixSpecs208.rowTargets (⟨10, by decide⟩ : Fin 14)) = true := by
  rw [BatchSourceLinear208.checkBlock_eq]
  apply BatchSource208.checkBlock_of_rowBlocks (width := 16) (chunks := 1)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact checkedPart000

theorem checked : BatchSource208.checkBlock FastDecode208.phi 2420 2429
    (SourcePrefixSpecs208.rowTargets (⟨10, by decide⟩ : Fin 14)) = true :=
  BatchSourceLinear208.checked checked_linear

#print axioms checked
end JSP233.SourcePrefix208_10_000


#check JSP233.SourcePrefix208_10_000.checked
