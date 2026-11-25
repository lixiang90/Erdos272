module

public import Erdos272.Arithmetic.N118533.RunChecks118533G0
public import Erdos272.Arithmetic.N118533.RunChecks118533G1
public import Erdos272.Arithmetic.N118533.RunChecks118533G2
public import Erdos272.Arithmetic.N118533.RunChecks118533G3

@[expose] public section

namespace JSP233.RunFacts118533
open RunSource118533 RunPlans118533
set_option autoImplicit false

theorem conditions {k : ℕ} (hk : k < 13) : Conditions (plan k) := by
  interval_cases k
  · exact RunChecks118533G0.conditions00
  · exact RunChecks118533G0.conditions01
  · exact RunChecks118533G0.conditions02
  · exact RunChecks118533G0.conditions03
  · exact RunChecks118533G1.conditions04
  · exact RunChecks118533G1.conditions05
  · exact RunChecks118533G1.conditions06
  · exact RunChecks118533G1.conditions07
  · exact RunChecks118533G2.conditions08
  · exact RunChecks118533G2.conditions09
  · exact RunChecks118533G2.conditions10
  · exact RunChecks118533G2.conditions11
  · exact RunChecks118533G3.conditions12

#print axioms conditions
end JSP233.RunFacts118533
