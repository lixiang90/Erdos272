module

public import Mathlib.Tactic.IntervalCases
public import Erdos272.Arithmetic.N65172.WitnessChecks65172G0
public import Erdos272.Arithmetic.N65172.WitnessChecks65172G1
public import Erdos272.Arithmetic.N65172.WitnessChecks65172G10
public import Erdos272.Arithmetic.N65172.WitnessChecks65172G2
public import Erdos272.Arithmetic.N65172.WitnessChecks65172G3
public import Erdos272.Arithmetic.N65172.WitnessChecks65172G4
public import Erdos272.Arithmetic.N65172.WitnessChecks65172G5
public import Erdos272.Arithmetic.N65172.WitnessChecks65172G6
public import Erdos272.Arithmetic.N65172.WitnessChecks65172G7
public import Erdos272.Arithmetic.N65172.WitnessChecks65172G8
public import Erdos272.Arithmetic.N65172.WitnessChecks65172G9

@[expose] public section

namespace JSP233.WitnessFacts65172
open WitnessNumeric65172
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem bound {k : ℕ} (hk : k<43) : value k≤(data k).cap := by
  interval_cases k
  · exact WitnessChecks65172G0.checked000
  · exact WitnessChecks65172G0.checked001
  · exact WitnessChecks65172G0.checked002
  · exact WitnessChecks65172G0.checked003
  · exact WitnessChecks65172G1.checked004
  · exact WitnessChecks65172G1.checked005
  · exact WitnessChecks65172G1.checked006
  · exact WitnessChecks65172G1.checked007
  · exact WitnessChecks65172G2.checked008
  · exact WitnessChecks65172G2.checked009
  · exact WitnessChecks65172G2.checked010
  · exact WitnessChecks65172G2.checked011
  · exact WitnessChecks65172G3.checked012
  · exact WitnessChecks65172G3.checked013
  · exact WitnessChecks65172G3.checked014
  · exact WitnessChecks65172G3.checked015
  · exact WitnessChecks65172G4.checked016
  · exact WitnessChecks65172G4.checked017
  · exact WitnessChecks65172G4.checked018
  · exact WitnessChecks65172G4.checked019
  · exact WitnessChecks65172G5.checked020
  · exact WitnessChecks65172G5.checked021
  · exact WitnessChecks65172G5.checked022
  · exact WitnessChecks65172G5.checked023
  · exact WitnessChecks65172G6.checked024
  · exact WitnessChecks65172G6.checked025
  · exact WitnessChecks65172G6.checked026
  · exact WitnessChecks65172G6.checked027
  · exact WitnessChecks65172G7.checked028
  · exact WitnessChecks65172G7.checked029
  · exact WitnessChecks65172G7.checked030
  · exact WitnessChecks65172G7.checked031
  · exact WitnessChecks65172G8.checked032
  · exact WitnessChecks65172G8.checked033
  · exact WitnessChecks65172G8.checked034
  · exact WitnessChecks65172G8.checked035
  · exact WitnessChecks65172G9.checked036
  · exact WitnessChecks65172G10.checked037
  · exact WitnessChecks65172G10.checked038
  · exact WitnessChecks65172G10.checked039
  · exact WitnessChecks65172G10.checked040
  · exact WitnessChecks65172G10.checked041
  · exact WitnessChecks65172G10.checked042

#print axioms bound
end
end JSP233.WitnessFacts65172
