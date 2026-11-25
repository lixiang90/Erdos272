module

public import Erdos272.Arithmetic.N65968.WitnessNumeric65968

@[expose] public section

namespace JSP233.WitnessChecks65968G2
open WitnessNumeric65968
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem checked008 : value 8≤data08.cap := by decide +kernel
#print axioms checked008

theorem checked009 : value 9≤data09.cap := by decide +kernel
#print axioms checked009

theorem checked010 : value 10≤data10.cap := by decide +kernel
#print axioms checked010

theorem checked011 : value 11≤data11.cap := by decide +kernel
#print axioms checked011

end
end JSP233.WitnessChecks65968G2
