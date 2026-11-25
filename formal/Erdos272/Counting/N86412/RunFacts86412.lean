module

public import Erdos272.Counting.N86412.RunPlans86412
public import Erdos272.Arithmetic.N86412.RunNumericChecks86412G0
public import Erdos272.Arithmetic.N86412.RunNumericChecks86412G1

@[expose] public section

namespace JSP233.RunFacts86412
set_option autoImplicit false

theorem conditions {k : ℕ} (hk : k < 21) :
    RunSource109474.Conditions (RunPlans86412.plan k) := by
  apply RunNumericBridge88404.conditions_sound
  interval_cases k
  · exact RunNumericChecks86412G0.conditions00
  · exact RunNumericChecks86412G0.conditions01
  · exact RunNumericChecks86412G0.conditions02
  · exact RunNumericChecks86412G0.conditions03
  · exact RunNumericChecks86412G0.conditions04
  · exact RunNumericChecks86412G0.conditions05
  · exact RunNumericChecks86412G0.conditions06
  · exact RunNumericChecks86412G0.conditions07
  · exact RunNumericChecks86412G0.conditions08
  · exact RunNumericChecks86412G0.conditions09
  · exact RunNumericChecks86412G0.conditions10
  · exact RunNumericChecks86412G0.conditions11
  · exact RunNumericChecks86412G0.conditions12
  · exact RunNumericChecks86412G0.conditions13
  · exact RunNumericChecks86412G0.conditions14
  · exact RunNumericChecks86412G0.conditions15
  · exact RunNumericChecks86412G1.conditions16
  · exact RunNumericChecks86412G1.conditions17
  · exact RunNumericChecks86412G1.conditions18
  · exact RunNumericChecks86412G1.conditions19
  · exact RunNumericChecks86412G1.conditions20

#print axioms conditions
end JSP233.RunFacts86412
