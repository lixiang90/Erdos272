module

public import Erdos272.Arithmetic.N291012.PrefixData291012

@[expose] public section

namespace JSP233.PrefixCalibration291012
open PrefixData291012 PrefixTableSound291012
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem p_zero : p 0 = 0 := by decide +kernel
theorem q_zero : q 0 = 0 := by decide +kernel
theorem recurrence_first : Check p q 0 256 = true := by decide +kernel
theorem recurrence_last : Check p q 29179 256 = true := by decide +kernel
theorem heavy_floor : FloorCheck p q 7424 7679 13 382482 = true := by decide +kernel

#print axioms p_zero
#print axioms q_zero
#print axioms recurrence_first
#print axioms recurrence_last
#print axioms heavy_floor
end JSP233.PrefixCalibration291012
