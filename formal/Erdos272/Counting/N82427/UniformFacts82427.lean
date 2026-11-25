module

public import Mathlib.Tactic.IntervalCases
public import Erdos272.Counting.N82427.UniformPlans82427
public import Erdos272.Arithmetic.N82427.UniformChecks82427G0
public import Erdos272.Arithmetic.N82427.UniformChecks82427G1
public import Erdos272.Arithmetic.N82427.UniformChecks82427G2

@[expose] public section

namespace JSP233.UniformFacts82427
open UniformNumeric84364 UniformPlans82427
set_option autoImplicit false

theorem bound {k : ℕ} (hk : k < 40) : (plan k).target ≤ value (plan k).lower := by
  interval_cases k
  · exact UniformChecks82427G0.checked00
  · exact UniformChecks82427G0.checked01
  · exact UniformChecks82427G0.checked02
  · exact UniformChecks82427G0.checked03
  · exact UniformChecks82427G0.checked04
  · exact UniformChecks82427G0.checked05
  · exact UniformChecks82427G0.checked06
  · exact UniformChecks82427G0.checked07
  · exact UniformChecks82427G0.checked08
  · exact UniformChecks82427G0.checked09
  · exact UniformChecks82427G0.checked10
  · exact UniformChecks82427G0.checked11
  · exact UniformChecks82427G0.checked12
  · exact UniformChecks82427G0.checked13
  · exact UniformChecks82427G0.checked14
  · exact UniformChecks82427G0.checked15
  · exact UniformChecks82427G1.checked16
  · exact UniformChecks82427G1.checked17
  · exact UniformChecks82427G1.checked18
  · exact UniformChecks82427G1.checked19
  · exact UniformChecks82427G1.checked20
  · exact UniformChecks82427G1.checked21
  · exact UniformChecks82427G1.checked22
  · exact UniformChecks82427G1.checked23
  · exact UniformChecks82427G1.checked24
  · exact UniformChecks82427G1.checked25
  · exact UniformChecks82427G1.checked26
  · exact UniformChecks82427G1.checked27
  · exact UniformChecks82427G1.checked28
  · exact UniformChecks82427G1.checked29
  · exact UniformChecks82427G1.checked30
  · exact UniformChecks82427G1.checked31
  · exact UniformChecks82427G2.checked32
  · exact UniformChecks82427G2.checked33
  · exact UniformChecks82427G2.checked34
  · exact UniformChecks82427G2.checked35
  · exact UniformChecks82427G2.checked36
  · exact UniformChecks82427G2.checked37
  · exact UniformChecks82427G2.checked38
  · exact UniformChecks82427G2.checked39

#print axioms bound

theorem sizes {k : ℕ} (hk : k < 40) : 4 ≤ (plan k).lower ∧ (plan k).lower ≤ 549 := by
  interval_cases k <;> decide +kernel
#print axioms sizes
end JSP233.UniformFacts82427
