module

public import Erdos272.Arithmetic.N65172.CleanupRows65172
public import Erdos272.Counting.N65968.IntegerFeeNat65968
public import Erdos272.Arithmetic.N65172.WitnessNumeric65172

@[expose] public section

namespace JSP233.ScalarUpper65172
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Upper (N k : ℕ) : ℝ := IntegerFeeNat65968.Upper N
  (CleanupRows65172.data k).residualUnits (CleanupRows65172.data k).total.net
  (WitnessNumeric65172.data k).cap
end
end JSP233.ScalarUpper65172
