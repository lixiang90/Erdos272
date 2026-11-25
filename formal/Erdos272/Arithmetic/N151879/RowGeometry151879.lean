module

public import Erdos272.Arithmetic.N151879.RowGeometryCertificates151879G0
public import Erdos272.Arithmetic.N151879.RowGeometryCertificates151879G1
public import Erdos272.Arithmetic.N291012.RowGeometry291012

@[expose] public section

namespace JSP233.RowGeometry151879
open CleanupRows151879 RowStatic291012
set_option autoImplicit false

theorem parameters {k : ℕ} (hk : k < 11) : Static (data k) := by
  interval_cases k
  · exact RowGeometryCertificates151879G0.static00
  · exact RowGeometryCertificates151879G0.static01
  · exact RowGeometryCertificates151879G0.static02
  · exact RowGeometryCertificates151879G0.static03
  · exact RowGeometryCertificates151879G0.static04
  · exact RowGeometryCertificates151879G0.static05
  · exact RowGeometryCertificates151879G0.static06
  · exact RowGeometryCertificates151879G0.static07
  · exact RowGeometryCertificates151879G0.static08
  · exact RowGeometryCertificates151879G0.static09
  · exact RowGeometryCertificates151879G1.static10

#print axioms parameters
end JSP233.RowGeometry151879
