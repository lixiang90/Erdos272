module

public import Erdos272.Arithmetic.N84364.RowGeometryCertificates84364G0
public import Erdos272.Arithmetic.N84364.RowGeometryCertificates84364G1
public import Erdos272.Arithmetic.N84364.RowGeometryCertificates84364G2
public import Erdos272.Arithmetic.N84364.RowGeometryCertificates84364G3
public import Erdos272.Arithmetic.N84364.RowGeometryCertificates84364G4
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry84364
open CleanupRows84364 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 43) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates84364G0.static00
  · exact RowGeometryCertificates84364G0.static01
  · exact RowGeometryCertificates84364G0.static02
  · exact RowGeometryCertificates84364G0.static03
  · exact RowGeometryCertificates84364G0.static04
  · exact RowGeometryCertificates84364G0.static05
  · exact RowGeometryCertificates84364G0.static06
  · exact RowGeometryCertificates84364G0.static07
  · exact RowGeometryCertificates84364G0.static08
  · exact RowGeometryCertificates84364G0.static09
  · exact RowGeometryCertificates84364G1.static10
  · exact RowGeometryCertificates84364G1.static11
  · exact RowGeometryCertificates84364G1.static12
  · exact RowGeometryCertificates84364G1.static13
  · exact RowGeometryCertificates84364G1.static14
  · exact RowGeometryCertificates84364G1.static15
  · exact RowGeometryCertificates84364G1.static16
  · exact RowGeometryCertificates84364G1.static17
  · exact RowGeometryCertificates84364G1.static18
  · exact RowGeometryCertificates84364G1.static19
  · exact RowGeometryCertificates84364G2.static20
  · exact RowGeometryCertificates84364G2.static21
  · exact RowGeometryCertificates84364G2.static22
  · exact RowGeometryCertificates84364G2.static23
  · exact RowGeometryCertificates84364G2.static24
  · exact RowGeometryCertificates84364G2.static25
  · exact RowGeometryCertificates84364G2.static26
  · exact RowGeometryCertificates84364G2.static27
  · exact RowGeometryCertificates84364G2.static28
  · exact RowGeometryCertificates84364G2.static29
  · exact RowGeometryCertificates84364G3.static30
  · exact RowGeometryCertificates84364G3.static31
  · exact RowGeometryCertificates84364G3.static32
  · exact RowGeometryCertificates84364G3.static33
  · exact RowGeometryCertificates84364G3.static34
  · exact RowGeometryCertificates84364G3.static35
  · exact RowGeometryCertificates84364G3.static36
  · exact RowGeometryCertificates84364G3.static37
  · exact RowGeometryCertificates84364G3.static38
  · exact RowGeometryCertificates84364G3.static39
  · exact RowGeometryCertificates84364G4.static40
  · exact RowGeometryCertificates84364G4.static41
  · exact RowGeometryCertificates84364G4.static42

#print axioms parameters
end JSP233.RowGeometry84364
