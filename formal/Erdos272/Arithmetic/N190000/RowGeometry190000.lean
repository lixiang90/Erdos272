module

public import Erdos272.Arithmetic.N190000.RowGeometryCertificates190000G0
public import Erdos272.Arithmetic.N190000.RowGeometryCertificates190000G1
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry190000
open CleanupRows190000 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 14) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates190000G0.static00
  · exact RowGeometryCertificates190000G0.static01
  · exact RowGeometryCertificates190000G0.static02
  · exact RowGeometryCertificates190000G0.static03
  · exact RowGeometryCertificates190000G0.static04
  · exact RowGeometryCertificates190000G0.static05
  · exact RowGeometryCertificates190000G0.static06
  · exact RowGeometryCertificates190000G0.static07
  · exact RowGeometryCertificates190000G0.static08
  · exact RowGeometryCertificates190000G0.static09
  · exact RowGeometryCertificates190000G1.static10
  · exact RowGeometryCertificates190000G1.static11
  · exact RowGeometryCertificates190000G1.static12
  · exact RowGeometryCertificates190000G1.static13

#print axioms parameters
end JSP233.RowGeometry190000
