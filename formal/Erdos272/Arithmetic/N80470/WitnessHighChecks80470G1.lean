module

public import Erdos272.Arithmetic.N80470.WitnessHighNumeric80470

@[expose] public section

namespace JSP233.WitnessHighChecks80470G1
open WitnessHighNumeric80470
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem checked04 : value data04 ≤ data04.cap := by decide +kernel
#print axioms checked04

theorem checked05 : value data05 ≤ data05.cap := by decide +kernel
#print axioms checked05

theorem checked06 : value data06 ≤ data06.cap := by decide +kernel
#print axioms checked06

theorem checked07 : value data07 ≤ data07.cap := by decide +kernel
#print axioms checked07

end JSP233.WitnessHighChecks80470G1
