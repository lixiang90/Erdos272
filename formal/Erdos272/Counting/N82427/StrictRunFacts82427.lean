module

public import Erdos272.Counting.N82427.StrictRunPlans82427
public import Erdos272.Arithmetic.N82427.StrictRunNumericChecks82427G0
public import Erdos272.Arithmetic.N82427.StrictRunNumericChecks82427G1
public import Erdos272.Arithmetic.N82427.StrictRunNumericChecks82427G2

@[expose] public section

namespace JSP233.StrictRunFacts82427
set_option autoImplicit false

theorem conditions {k : ℕ} (hk : k < 38) :
    StrictRunSource86412.Conditions (StrictRunPlans82427.plan k) := by
  apply StrictRunNumericBridge86412.conditions_sound
  interval_cases k
  · exact StrictRunNumericChecks82427G0.conditions00
  · exact StrictRunNumericChecks82427G0.conditions01
  · exact StrictRunNumericChecks82427G0.conditions02
  · exact StrictRunNumericChecks82427G0.conditions03
  · exact StrictRunNumericChecks82427G0.conditions04
  · exact StrictRunNumericChecks82427G0.conditions05
  · exact StrictRunNumericChecks82427G0.conditions06
  · exact StrictRunNumericChecks82427G0.conditions07
  · exact StrictRunNumericChecks82427G0.conditions08
  · exact StrictRunNumericChecks82427G0.conditions09
  · exact StrictRunNumericChecks82427G0.conditions10
  · exact StrictRunNumericChecks82427G0.conditions11
  · exact StrictRunNumericChecks82427G0.conditions12
  · exact StrictRunNumericChecks82427G0.conditions13
  · exact StrictRunNumericChecks82427G0.conditions14
  · exact StrictRunNumericChecks82427G0.conditions15
  · exact StrictRunNumericChecks82427G1.conditions16
  · exact StrictRunNumericChecks82427G1.conditions17
  · exact StrictRunNumericChecks82427G1.conditions18
  · exact StrictRunNumericChecks82427G1.conditions19
  · exact StrictRunNumericChecks82427G1.conditions20
  · exact StrictRunNumericChecks82427G1.conditions21
  · exact StrictRunNumericChecks82427G1.conditions22
  · exact StrictRunNumericChecks82427G1.conditions23
  · exact StrictRunNumericChecks82427G1.conditions24
  · exact StrictRunNumericChecks82427G1.conditions25
  · exact StrictRunNumericChecks82427G1.conditions26
  · exact StrictRunNumericChecks82427G1.conditions27
  · exact StrictRunNumericChecks82427G1.conditions28
  · exact StrictRunNumericChecks82427G1.conditions29
  · exact StrictRunNumericChecks82427G1.conditions30
  · exact StrictRunNumericChecks82427G1.conditions31
  · exact StrictRunNumericChecks82427G2.conditions32
  · exact StrictRunNumericChecks82427G2.conditions33
  · exact StrictRunNumericChecks82427G2.conditions34
  · exact StrictRunNumericChecks82427G2.conditions35
  · exact StrictRunNumericChecks82427G2.conditions36
  · exact StrictRunNumericChecks82427G2.conditions37

#print axioms conditions
end JSP233.StrictRunFacts82427
