module

public import Erdos272.Arithmetic.N142758.RowGeometryCertificates142758G0
public import Erdos272.Arithmetic.N142758.RowGeometryCertificates142758G1
public import Erdos272.Arithmetic.N142758.RowGeometryCertificates142758G2
public import Erdos272.Arithmetic.N142758.RowGeometryCertificates142758G3
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry142758
open CleanupRows142758 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 38) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates142758G0.static00
  · exact RowGeometryCertificates142758G0.static01
  · exact RowGeometryCertificates142758G0.static02
  · exact RowGeometryCertificates142758G0.static03
  · exact RowGeometryCertificates142758G0.static04
  · exact RowGeometryCertificates142758G0.static05
  · exact RowGeometryCertificates142758G0.static06
  · exact RowGeometryCertificates142758G0.static07
  · exact RowGeometryCertificates142758G0.static08
  · exact RowGeometryCertificates142758G0.static09
  · exact RowGeometryCertificates142758G1.static10
  · exact RowGeometryCertificates142758G1.static11
  · exact RowGeometryCertificates142758G1.static12
  · exact RowGeometryCertificates142758G1.static13
  · exact RowGeometryCertificates142758G1.static14
  · exact RowGeometryCertificates142758G1.static15
  · exact RowGeometryCertificates142758G1.static16
  · exact RowGeometryCertificates142758G1.static17
  · exact RowGeometryCertificates142758G1.static18
  · exact RowGeometryCertificates142758G1.static19
  · exact RowGeometryCertificates142758G2.static20
  · exact RowGeometryCertificates142758G2.static21
  · exact RowGeometryCertificates142758G2.static22
  · exact RowGeometryCertificates142758G2.static23
  · exact RowGeometryCertificates142758G2.static24
  · exact RowGeometryCertificates142758G2.static25
  · exact RowGeometryCertificates142758G2.static26
  · exact RowGeometryCertificates142758G2.static27
  · exact RowGeometryCertificates142758G2.static28
  · exact RowGeometryCertificates142758G2.static29
  · exact RowGeometryCertificates142758G3.static30
  · exact RowGeometryCertificates142758G3.static31
  · exact RowGeometryCertificates142758G3.static32
  · exact RowGeometryCertificates142758G3.static33
  · exact RowGeometryCertificates142758G3.static34
  · exact RowGeometryCertificates142758G3.static35
  · exact RowGeometryCertificates142758G3.static36
  · exact RowGeometryCertificates142758G3.static37

#print axioms parameters
end JSP233.RowGeometry142758
