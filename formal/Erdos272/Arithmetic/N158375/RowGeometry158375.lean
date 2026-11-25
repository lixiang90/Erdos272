module

public import Erdos272.Arithmetic.N158375.RowGeometryCertificates158375G0
public import Erdos272.Arithmetic.N158375.RowGeometryCertificates158375G1
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry158375
open CleanupRows158375 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 20) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates158375G0.static00
  · exact RowGeometryCertificates158375G0.static01
  · exact RowGeometryCertificates158375G0.static02
  · exact RowGeometryCertificates158375G0.static03
  · exact RowGeometryCertificates158375G0.static04
  · exact RowGeometryCertificates158375G0.static05
  · exact RowGeometryCertificates158375G0.static06
  · exact RowGeometryCertificates158375G0.static07
  · exact RowGeometryCertificates158375G0.static08
  · exact RowGeometryCertificates158375G0.static09
  · exact RowGeometryCertificates158375G1.static10
  · exact RowGeometryCertificates158375G1.static11
  · exact RowGeometryCertificates158375G1.static12
  · exact RowGeometryCertificates158375G1.static13
  · exact RowGeometryCertificates158375G1.static14
  · exact RowGeometryCertificates158375G1.static15
  · exact RowGeometryCertificates158375G1.static16
  · exact RowGeometryCertificates158375G1.static17
  · exact RowGeometryCertificates158375G1.static18
  · exact RowGeometryCertificates158375G1.static19

#print axioms parameters
end JSP233.RowGeometry158375
