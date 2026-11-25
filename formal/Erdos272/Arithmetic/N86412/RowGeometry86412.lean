module

public import Erdos272.Arithmetic.N86412.RowGeometryCertificates86412G0
public import Erdos272.Arithmetic.N86412.RowGeometryCertificates86412G1
public import Erdos272.Arithmetic.N86412.RowGeometryCertificates86412G2
public import Erdos272.Arithmetic.N86412.RowGeometryCertificates86412G3
public import Erdos272.Arithmetic.N86412.RowGeometryCertificates86412G4
public import Erdos272.Arithmetic.N86412.RowGeometryCertificates86412G5
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry86412
open CleanupRows86412 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 51) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates86412G0.static00
  · exact RowGeometryCertificates86412G0.static01
  · exact RowGeometryCertificates86412G0.static02
  · exact RowGeometryCertificates86412G0.static03
  · exact RowGeometryCertificates86412G0.static04
  · exact RowGeometryCertificates86412G0.static05
  · exact RowGeometryCertificates86412G0.static06
  · exact RowGeometryCertificates86412G0.static07
  · exact RowGeometryCertificates86412G0.static08
  · exact RowGeometryCertificates86412G0.static09
  · exact RowGeometryCertificates86412G1.static10
  · exact RowGeometryCertificates86412G1.static11
  · exact RowGeometryCertificates86412G1.static12
  · exact RowGeometryCertificates86412G1.static13
  · exact RowGeometryCertificates86412G1.static14
  · exact RowGeometryCertificates86412G1.static15
  · exact RowGeometryCertificates86412G1.static16
  · exact RowGeometryCertificates86412G1.static17
  · exact RowGeometryCertificates86412G1.static18
  · exact RowGeometryCertificates86412G1.static19
  · exact RowGeometryCertificates86412G2.static20
  · exact RowGeometryCertificates86412G2.static21
  · exact RowGeometryCertificates86412G2.static22
  · exact RowGeometryCertificates86412G2.static23
  · exact RowGeometryCertificates86412G2.static24
  · exact RowGeometryCertificates86412G2.static25
  · exact RowGeometryCertificates86412G2.static26
  · exact RowGeometryCertificates86412G2.static27
  · exact RowGeometryCertificates86412G2.static28
  · exact RowGeometryCertificates86412G2.static29
  · exact RowGeometryCertificates86412G3.static30
  · exact RowGeometryCertificates86412G3.static31
  · exact RowGeometryCertificates86412G3.static32
  · exact RowGeometryCertificates86412G3.static33
  · exact RowGeometryCertificates86412G3.static34
  · exact RowGeometryCertificates86412G3.static35
  · exact RowGeometryCertificates86412G3.static36
  · exact RowGeometryCertificates86412G3.static37
  · exact RowGeometryCertificates86412G3.static38
  · exact RowGeometryCertificates86412G3.static39
  · exact RowGeometryCertificates86412G4.static40
  · exact RowGeometryCertificates86412G4.static41
  · exact RowGeometryCertificates86412G4.static42
  · exact RowGeometryCertificates86412G4.static43
  · exact RowGeometryCertificates86412G4.static44
  · exact RowGeometryCertificates86412G4.static45
  · exact RowGeometryCertificates86412G4.static46
  · exact RowGeometryCertificates86412G4.static47
  · exact RowGeometryCertificates86412G4.static48
  · exact RowGeometryCertificates86412G4.static49
  · exact RowGeometryCertificates86412G5.static50

#print axioms parameters
end JSP233.RowGeometry86412
