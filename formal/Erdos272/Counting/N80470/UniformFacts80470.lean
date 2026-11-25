module

public import Mathlib.Tactic.IntervalCases
public import Erdos272.Counting.N80470.UniformPlans80470
public import Erdos272.Arithmetic.N80470.UniformChecks80470G0

@[expose] public section

namespace JSP233.UniformFacts80470
open UniformNumeric84364 UniformPlans80470
set_option autoImplicit false

theorem bound {k : ℕ} (hk : k < 5) : (plan k).target ≤ value (plan k).lower := by
  interval_cases k
  · exact UniformChecks80470G0.checked00
  · exact UniformChecks80470G0.checked01
  · exact UniformChecks80470G0.checked02
  · exact UniformChecks80470G0.checked03
  · exact UniformChecks80470G0.checked04

#print axioms bound

theorem sizes {k : ℕ} (hk : k < 5) : 4 ≤ (plan k).lower ∧ (plan k).lower ≤ 549 := by
  interval_cases k <;> decide +kernel
#print axioms sizes
end JSP233.UniformFacts80470
