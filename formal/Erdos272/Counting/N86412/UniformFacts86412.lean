module

public import Erdos272.Arithmetic.N86412.UniformChecks86412G0
public import Erdos272.Arithmetic.N86412.UniformChecks86412G1
public import Erdos272.Arithmetic.N86412.UniformChecks86412G2
public import Erdos272.Arithmetic.N86412.UniformChecks86412G3

@[expose] public section

namespace JSP233.UniformFacts86412
open UniformEval86412 UniformPlans86412
set_option autoImplicit false

theorem bound {k : ℕ} (hk : k < 54) :
    (plan k).target ≤ value (plan k).lower := by
  interval_cases k
  · exact UniformChecks86412G0.checked00
  · exact UniformChecks86412G0.checked01
  · exact UniformChecks86412G0.checked02
  · exact UniformChecks86412G0.checked03
  · exact UniformChecks86412G0.checked04
  · exact UniformChecks86412G0.checked05
  · exact UniformChecks86412G0.checked06
  · exact UniformChecks86412G0.checked07
  · exact UniformChecks86412G1.checked08
  · exact UniformChecks86412G1.checked09
  · exact UniformChecks86412G1.checked10
  · exact UniformChecks86412G1.checked11
  · exact UniformChecks86412G1.checked12
  · exact UniformChecks86412G1.checked13
  · exact UniformChecks86412G1.checked14
  · exact UniformChecks86412G1.checked15
  · exact UniformChecks86412G1.checked16
  · exact UniformChecks86412G1.checked17
  · exact UniformChecks86412G1.checked18
  · exact UniformChecks86412G1.checked19
  · exact UniformChecks86412G1.checked20
  · exact UniformChecks86412G1.checked21
  · exact UniformChecks86412G1.checked22
  · exact UniformChecks86412G1.checked23
  · exact UniformChecks86412G2.checked24
  · exact UniformChecks86412G2.checked25
  · exact UniformChecks86412G2.checked26
  · exact UniformChecks86412G2.checked27
  · exact UniformChecks86412G2.checked28
  · exact UniformChecks86412G2.checked29
  · exact UniformChecks86412G2.checked30
  · exact UniformChecks86412G2.checked31
  · exact UniformChecks86412G2.checked32
  · exact UniformChecks86412G2.checked33
  · exact UniformChecks86412G2.checked34
  · exact UniformChecks86412G2.checked35
  · exact UniformChecks86412G2.checked36
  · exact UniformChecks86412G2.checked37
  · exact UniformChecks86412G2.checked38
  · exact UniformChecks86412G2.checked39
  · exact UniformChecks86412G3.checked40
  · exact UniformChecks86412G3.checked41
  · exact UniformChecks86412G3.checked42
  · exact UniformChecks86412G3.checked43
  · exact UniformChecks86412G3.checked44
  · exact UniformChecks86412G3.checked45
  · exact UniformChecks86412G3.checked46
  · exact UniformChecks86412G3.checked47
  · exact UniformChecks86412G3.checked48
  · exact UniformChecks86412G3.checked49
  · exact UniformChecks86412G3.checked50
  · exact UniformChecks86412G3.checked51
  · exact UniformChecks86412G3.checked52
  · exact UniformChecks86412G3.checked53

#print axioms bound

theorem sizes {k : ℕ} (hk : k < 54) :
    4 ≤ (plan k).lower ∧ (plan k).lower ≤ 32753 := by
  interval_cases k <;> decide +kernel

#print axioms sizes
end JSP233.UniformFacts86412
