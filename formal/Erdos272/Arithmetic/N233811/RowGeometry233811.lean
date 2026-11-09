module

public import Erdos272.Arithmetic.N233811.RowGeometryCertificates233811G0
public import Erdos272.Arithmetic.N233811.RowGeometryCertificates233811G1
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry233811
open CleanupRows233811 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 12) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates233811G0.static00
  · exact RowGeometryCertificates233811G0.static01
  · exact RowGeometryCertificates233811G0.static02
  · exact RowGeometryCertificates233811G0.static03
  · exact RowGeometryCertificates233811G0.static04
  · exact RowGeometryCertificates233811G0.static05
  · exact RowGeometryCertificates233811G0.static06
  · exact RowGeometryCertificates233811G0.static07
  · exact RowGeometryCertificates233811G0.static08
  · exact RowGeometryCertificates233811G0.static09
  · exact RowGeometryCertificates233811G1.static10
  · exact RowGeometryCertificates233811G1.static11

#print axioms parameters
end JSP233.RowGeometry233811
