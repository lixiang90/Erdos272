module

public import Erdos272.Arithmetic.N80470.WitnessHighNumeric80470

@[expose] public section

namespace JSP233.WitnessHighChecks80470G2
open WitnessHighNumeric80470
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem checked08 : value data08 ≤ data08.cap := by decide +kernel
#print axioms checked08

theorem checked09 : value data09 ≤ data09.cap := by decide +kernel
#print axioms checked09

theorem checked10 : value data10 ≤ data10.cap := by decide +kernel
#print axioms checked10

theorem checked11 : value data11 ≤ data11.cap := by decide +kernel
#print axioms checked11

end JSP233.WitnessHighChecks80470G2
