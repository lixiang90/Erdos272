module

public import Mathlib.Tactic.IntervalCases
public import Erdos272.Counting.N84364.UniformPlans84364
public import Erdos272.Arithmetic.N84364.UniformChecks84364G0
public import Erdos272.Arithmetic.N84364.UniformChecks84364G1

@[expose] public section

namespace JSP233.UniformFacts84364
open UniformNumeric84364 UniformPlans84364
set_option autoImplicit false

theorem bound {k : ℕ} (hk : k < 23) :
    (plan k).target ≤ value (plan k).lower := by
  interval_cases k
  · exact UniformNumericPilot84364.checked0
  · exact UniformNumericPilot84364.checked1
  · exact UniformNumericPilot84364.checked3
  · exact UniformChecks84364G0.checked03
  · exact UniformChecks84364G0.checked04
  · exact UniformChecks84364G0.checked05
  · exact UniformChecks84364G0.checked06
  · exact UniformChecks84364G0.checked07
  · exact UniformChecks84364G0.checked08
  · exact UniformChecks84364G0.checked09
  · exact UniformChecks84364G0.checked10
  · exact UniformChecks84364G0.checked11
  · exact UniformChecks84364G0.checked12
  · exact UniformChecks84364G0.checked13
  · exact UniformChecks84364G0.checked14
  · exact UniformChecks84364G0.checked15
  · exact UniformChecks84364G0.checked16
  · exact UniformChecks84364G0.checked17
  · exact UniformChecks84364G0.checked18
  · exact UniformChecks84364G1.checked19
  · exact UniformChecks84364G1.checked20
  · exact UniformChecks84364G1.checked21
  · exact UniformChecks84364G1.checked22

#print axioms bound

theorem sizes {k : ℕ} (hk : k < 23) :
    4 ≤ (plan k).lower ∧ (plan k).lower ≤ 549 := by
  interval_cases k <;> decide +kernel

#print axioms sizes
end JSP233.UniformFacts84364
