module

public import Erdos272.Arithmetic.N150465.RowGeometryCertificates150465G0
public import Erdos272.Arithmetic.N150465.RowGeometryCertificates150465G1
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry150465
open CleanupRows150465 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 12) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates150465G0.static00
  · exact RowGeometryCertificates150465G0.static01
  · exact RowGeometryCertificates150465G0.static02
  · exact RowGeometryCertificates150465G0.static03
  · exact RowGeometryCertificates150465G0.static04
  · exact RowGeometryCertificates150465G0.static05
  · exact RowGeometryCertificates150465G0.static06
  · exact RowGeometryCertificates150465G0.static07
  · exact RowGeometryCertificates150465G0.static08
  · exact RowGeometryCertificates150465G0.static09
  · exact RowGeometryCertificates150465G1.static10
  · exact RowGeometryCertificates150465G1.static11

#print axioms parameters
end JSP233.RowGeometry150465
