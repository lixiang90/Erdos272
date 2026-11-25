module

public import Erdos272.Counting.N84364.StrictRunPlans84364
public import Erdos272.Arithmetic.N84364.StrictRunNumericChecks84364G0
public import Erdos272.Arithmetic.N84364.StrictRunNumericChecks84364G1

@[expose] public section

namespace JSP233.StrictRunFacts84364
set_option autoImplicit false

theorem conditions {k : ℕ} (hk : k < 24) :
    StrictRunSource86412.Conditions (StrictRunPlans84364.plan k) := by
  apply StrictRunNumericBridge86412.conditions_sound
  interval_cases k
  · exact StrictRunNumericChecks84364G0.conditions00
  · exact StrictRunNumericChecks84364G0.conditions01
  · exact StrictRunNumericChecks84364G0.conditions02
  · exact StrictRunNumericChecks84364G0.conditions03
  · exact StrictRunNumericChecks84364G0.conditions04
  · exact StrictRunNumericChecks84364G0.conditions05
  · exact StrictRunNumericChecks84364G0.conditions06
  · exact StrictRunNumericChecks84364G0.conditions07
  · exact StrictRunNumericChecks84364G0.conditions08
  · exact StrictRunNumericChecks84364G0.conditions09
  · exact StrictRunNumericChecks84364G0.conditions10
  · exact StrictRunNumericChecks84364G0.conditions11
  · exact StrictRunNumericChecks84364G0.conditions12
  · exact StrictRunNumericChecks84364G0.conditions13
  · exact StrictRunNumericChecks84364G0.conditions14
  · exact StrictRunNumericChecks84364G0.conditions15
  · exact StrictRunNumericChecks84364G1.conditions16
  · exact StrictRunNumericChecks84364G1.conditions17
  · exact StrictRunNumericChecks84364G1.conditions18
  · exact StrictRunNumericChecks84364G1.conditions19
  · exact StrictRunNumericChecks84364G1.conditions20
  · exact StrictRunNumericChecks84364G1.conditions21
  · exact StrictRunNumericChecks84364G1.conditions22
  · exact StrictRunNumericChecks84364G1.conditions23

#print axioms conditions
end JSP233.StrictRunFacts84364
