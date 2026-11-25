module

public import Erdos272.Arithmetic.N153080.RowGeometryCertificates153080G0
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry153080
open CleanupRows153080 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 9) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates153080G0.static00
  · exact RowGeometryCertificates153080G0.static01
  · exact RowGeometryCertificates153080G0.static02
  · exact RowGeometryCertificates153080G0.static03
  · exact RowGeometryCertificates153080G0.static04
  · exact RowGeometryCertificates153080G0.static05
  · exact RowGeometryCertificates153080G0.static06
  · exact RowGeometryCertificates153080G0.static07
  · exact RowGeometryCertificates153080G0.static08

#print axioms parameters
end JSP233.RowGeometry153080
