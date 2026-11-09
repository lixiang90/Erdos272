module

public import Erdos272.Arithmetic.N243614.RowGeometryCertificates243614G0
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry243614
open CleanupRows243614 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 5) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates243614G0.static00
  · exact RowGeometryCertificates243614G0.static01
  · exact RowGeometryCertificates243614G0.static02
  · exact RowGeometryCertificates243614G0.static03
  · exact RowGeometryCertificates243614G0.static04

#print axioms parameters
end JSP233.RowGeometry243614
