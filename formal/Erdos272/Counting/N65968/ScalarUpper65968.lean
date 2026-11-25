module

public import Erdos272.Arithmetic.N65968.CleanupRows65968
public import Erdos272.Counting.N65968.IntegerFeeNat65968
public import Erdos272.Arithmetic.N65968.WitnessNumeric65968

@[expose] public section

namespace JSP233.ScalarUpper65968
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Upper (N k : ℕ) : ℝ := IntegerFeeNat65968.Upper N
  (CleanupRows65968.data k).residualUnits (CleanupRows65968.data k).total.net
  (WitnessNumeric65968.data k).cap
end
end JSP233.ScalarUpper65968
