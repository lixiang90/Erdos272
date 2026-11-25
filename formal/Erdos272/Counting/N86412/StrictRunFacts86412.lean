module

public import Erdos272.Counting.N86412.StrictRunPlans86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericChecks86412G0

@[expose] public section

namespace JSP233.StrictRunFacts86412
set_option autoImplicit false

theorem conditions {k : ℕ} (hk : k < 16) :
    StrictRunSource86412.Conditions (StrictRunPlans86412.plan k) := by
  apply StrictRunNumericBridge86412.conditions_sound
  interval_cases k
  · exact StrictRunNumericChecks86412G0.conditions00
  · exact StrictRunNumericChecks86412G0.conditions01
  · exact StrictRunNumericChecks86412G0.conditions02
  · exact StrictRunNumericChecks86412G0.conditions03
  · exact StrictRunNumericChecks86412G0.conditions04
  · exact StrictRunNumericChecks86412G0.conditions05
  · exact StrictRunNumericChecks86412G0.conditions06
  · exact StrictRunNumericChecks86412G0.conditions07
  · exact StrictRunNumericChecks86412G0.conditions08
  · exact StrictRunNumericChecks86412G0.conditions09
  · exact StrictRunNumericChecks86412G0.conditions10
  · exact StrictRunNumericChecks86412G0.conditions11
  · exact StrictRunNumericChecks86412G0.conditions12
  · exact StrictRunNumericChecks86412G0.conditions13
  · exact StrictRunNumericChecks86412G0.conditions14
  · exact StrictRunNumericChecks86412G0.conditions15

#print axioms conditions
end JSP233.StrictRunFacts86412
