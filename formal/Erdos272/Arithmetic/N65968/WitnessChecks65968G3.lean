module

public import Erdos272.Arithmetic.N65968.WitnessNumeric65968

@[expose] public section

namespace JSP233.WitnessChecks65968G3
open WitnessNumeric65968
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem checked012 : value 12≤data12.cap := by decide +kernel
#print axioms checked012

theorem checked013 : value 13≤data13.cap := by decide +kernel
#print axioms checked013

theorem checked014 : value 14≤data14.cap := by decide +kernel
#print axioms checked014

theorem checked015 : value 15≤data15.cap := by decide +kernel
#print axioms checked015

end
end JSP233.WitnessChecks65968G3
