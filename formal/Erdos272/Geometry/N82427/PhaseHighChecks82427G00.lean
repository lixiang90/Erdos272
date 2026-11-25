module

public import Erdos272.Geometry.N82427.PhaseNumeric82427

@[expose] public section

namespace JSP233.PhaseHighChecks82427G00
open PhaseNumeric82427
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem checked00 : value (data 0) ≤ (data 0).cap := by decide +kernel
#print axioms checked00

theorem checked01 : value (data 1) ≤ (data 1).cap := by decide +kernel
#print axioms checked01

theorem checked02 : value (data 2) ≤ (data 2).cap := by decide +kernel
#print axioms checked02

theorem checked03 : value (data 3) ≤ (data 3).cap := by decide +kernel
#print axioms checked03

end JSP233.PhaseHighChecks82427G00
