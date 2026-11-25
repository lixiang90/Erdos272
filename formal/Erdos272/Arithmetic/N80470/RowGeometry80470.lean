module

public import Erdos272.Arithmetic.N80470.RowGeometryCertificates80470G0
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry80470
open CleanupRows80470 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 20) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates80470G0.static00
  · exact RowGeometryCertificates80470G0.static01
  · exact RowGeometryCertificates80470G0.static02
  · exact RowGeometryCertificates80470G0.static03
  · exact RowGeometryCertificates80470G0.static04
  · exact RowGeometryCertificates80470G0.static05
  · exact RowGeometryCertificates80470G0.static06
  · exact RowGeometryCertificates80470G0.static07
  · exact RowGeometryCertificates80470G0.static08
  · exact RowGeometryCertificates80470G0.static09
  · exact RowGeometryCertificates80470G0.static10
  · exact RowGeometryCertificates80470G0.static11
  · exact RowGeometryCertificates80470G0.static12
  · exact RowGeometryCertificates80470G0.static13
  · exact RowGeometryCertificates80470G0.static14
  · exact RowGeometryCertificates80470G0.static15
  · exact RowGeometryCertificates80470G0.static16
  · exact RowGeometryCertificates80470G0.static17
  · exact RowGeometryCertificates80470G0.static18
  · exact RowGeometryCertificates80470G0.static19

#print axioms parameters
end JSP233.RowGeometry80470
