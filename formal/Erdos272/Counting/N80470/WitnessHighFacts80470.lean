module

public import Mathlib.Tactic.IntervalCases
public import Erdos272.Arithmetic.N80470.WitnessHighChecks80470G0
public import Erdos272.Arithmetic.N80470.WitnessHighChecks80470G1
public import Erdos272.Arithmetic.N80470.WitnessHighChecks80470G2
public import Erdos272.Arithmetic.N80470.WitnessHighChecks80470G3
public import Erdos272.Arithmetic.N80470.WitnessHighChecks80470G4

@[expose] public section

namespace JSP233.WitnessHighFacts80470
open WitnessHighNumeric80470
theorem bound {k : ℕ} (hk : k < 20) : value (data k) ≤ (data k).cap := by
  interval_cases k
  · exact WitnessHighChecks80470G0.checked00
  · exact WitnessHighChecks80470G0.checked01
  · exact WitnessHighChecks80470G0.checked02
  · exact WitnessHighChecks80470G0.checked03
  · exact WitnessHighChecks80470G1.checked04
  · exact WitnessHighChecks80470G1.checked05
  · exact WitnessHighChecks80470G1.checked06
  · exact WitnessHighChecks80470G1.checked07
  · exact WitnessHighChecks80470G2.checked08
  · exact WitnessHighChecks80470G2.checked09
  · exact WitnessHighChecks80470G2.checked10
  · exact WitnessHighChecks80470G2.checked11
  · exact WitnessHighChecks80470G3.checked12
  · exact WitnessHighChecks80470G3.checked13
  · exact WitnessHighChecks80470G3.checked14
  · exact WitnessHighChecks80470G3.checked15
  · exact WitnessHighChecks80470G4.checked16
  · exact WitnessHighChecks80470G4.checked17
  · exact WitnessHighChecks80470G4.checked18
  · exact WitnessHighChecks80470G4.checked19
#print axioms bound
end JSP233.WitnessHighFacts80470
