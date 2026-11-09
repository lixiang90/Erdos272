module

public import Erdos272.Arithmetic.N250262.RowGeometryCertificates250262G0
public import Erdos272.Arithmetic.N250262.RowGeometryCertificates250262G1
public import Erdos272.Arithmetic.N250262.RowGeometryCertificates250262G2
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry250262
open CleanupRows250262 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 28) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates250262G0.static00
  · exact RowGeometryCertificates250262G0.static01
  · exact RowGeometryCertificates250262G0.static02
  · exact RowGeometryCertificates250262G0.static03
  · exact RowGeometryCertificates250262G0.static04
  · exact RowGeometryCertificates250262G0.static05
  · exact RowGeometryCertificates250262G0.static06
  · exact RowGeometryCertificates250262G0.static07
  · exact RowGeometryCertificates250262G0.static08
  · exact RowGeometryCertificates250262G0.static09
  · exact RowGeometryCertificates250262G1.static10
  · exact RowGeometryCertificates250262G1.static11
  · exact RowGeometryCertificates250262G1.static12
  · exact RowGeometryCertificates250262G1.static13
  · exact RowGeometryCertificates250262G1.static14
  · exact RowGeometryCertificates250262G1.static15
  · exact RowGeometryCertificates250262G1.static16
  · exact RowGeometryCertificates250262G1.static17
  · exact RowGeometryCertificates250262G1.static18
  · exact RowGeometryCertificates250262G1.static19
  · exact RowGeometryCertificates250262G2.static20
  · exact RowGeometryCertificates250262G2.static21
  · exact RowGeometryCertificates250262G2.static22
  · exact RowGeometryCertificates250262G2.static23
  · exact RowGeometryCertificates250262G2.static24
  · exact RowGeometryCertificates250262G2.static25
  · exact RowGeometryCertificates250262G2.static26
  · exact RowGeometryCertificates250262G2.static27

#print axioms parameters
end JSP233.RowGeometry250262
