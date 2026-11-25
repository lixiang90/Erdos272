module

public import Erdos272.Arithmetic.N155716.RowGeometryCertificates155716G0
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry155716
open CleanupRows155716 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 9) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates155716G0.static00
  · exact RowGeometryCertificates155716G0.static01
  · exact RowGeometryCertificates155716G0.static02
  · exact RowGeometryCertificates155716G0.static03
  · exact RowGeometryCertificates155716G0.static04
  · exact RowGeometryCertificates155716G0.static05
  · exact RowGeometryCertificates155716G0.static06
  · exact RowGeometryCertificates155716G0.static07
  · exact RowGeometryCertificates155716G0.static08

#print axioms parameters
end JSP233.RowGeometry155716
