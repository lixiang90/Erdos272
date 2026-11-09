module

public import Erdos272.Arithmetic.N200000.RowGeometryCertificates200000G0
public import Erdos272.Arithmetic.N200000.RowGeometryCertificates200000G1
public import Erdos272.Arithmetic.N200000.RowGeometryCertificates200000G2
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry200000
open CleanupRows200000 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 21) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates200000G0.static00
  · exact RowGeometryCertificates200000G0.static01
  · exact RowGeometryCertificates200000G0.static02
  · exact RowGeometryCertificates200000G0.static03
  · exact RowGeometryCertificates200000G0.static04
  · exact RowGeometryCertificates200000G0.static05
  · exact RowGeometryCertificates200000G0.static06
  · exact RowGeometryCertificates200000G0.static07
  · exact RowGeometryCertificates200000G0.static08
  · exact RowGeometryCertificates200000G0.static09
  · exact RowGeometryCertificates200000G1.static10
  · exact RowGeometryCertificates200000G1.static11
  · exact RowGeometryCertificates200000G1.static12
  · exact RowGeometryCertificates200000G1.static13
  · exact RowGeometryCertificates200000G1.static14
  · exact RowGeometryCertificates200000G1.static15
  · exact RowGeometryCertificates200000G1.static16
  · exact RowGeometryCertificates200000G1.static17
  · exact RowGeometryCertificates200000G1.static18
  · exact RowGeometryCertificates200000G1.static19
  · exact RowGeometryCertificates200000G2.static20

#print axioms parameters
end JSP233.RowGeometry200000
