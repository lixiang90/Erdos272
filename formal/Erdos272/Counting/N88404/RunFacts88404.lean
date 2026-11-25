module

public import Erdos272.Counting.N88404.RunPlans88404
public import Erdos272.Arithmetic.N88404.RunNumericChecks88404G0
public import Erdos272.Arithmetic.N88404.RunNumericChecks88404G1
public import Erdos272.Arithmetic.N88404.RunNumericChecks88404G2
public import Erdos272.Arithmetic.N88404.RunNumericChecks88404G3
public import Erdos272.Arithmetic.N88404.RunNumericChecks88404G4
public import Erdos272.Arithmetic.N88404.RunNumericChecks88404G5

@[expose] public section

namespace JSP233.RunFacts88404
set_option autoImplicit false

theorem conditions {k : ℕ} (hk : k < 75) :
    RunSource109474.Conditions (RunPlans88404.plan k) := by
  apply RunNumericBridge88404.conditions_sound
  interval_cases k
  · exact RunNumericChecks88404G0.conditions00
  · exact RunNumericChecks88404G0.conditions01
  · exact RunNumericChecks88404G0.conditions02
  · exact RunNumericChecks88404G0.conditions03
  · exact RunNumericChecks88404G1.conditions04
  · exact RunNumericChecks88404G1.conditions05
  · exact RunNumericChecks88404G1.conditions06
  · exact RunNumericChecks88404G1.conditions07
  · exact RunNumericChecks88404G1.conditions08
  · exact RunNumericChecks88404G1.conditions09
  · exact RunNumericChecks88404G1.conditions10
  · exact RunNumericChecks88404G1.conditions11
  · exact RunNumericChecks88404G1.conditions12
  · exact RunNumericChecks88404G1.conditions13
  · exact RunNumericChecks88404G1.conditions14
  · exact RunNumericChecks88404G1.conditions15
  · exact RunNumericChecks88404G1.conditions16
  · exact RunNumericChecks88404G1.conditions17
  · exact RunNumericChecks88404G1.conditions18
  · exact RunNumericChecks88404G1.conditions19
  · exact RunNumericChecks88404G2.conditions20
  · exact RunNumericChecks88404G2.conditions21
  · exact RunNumericChecks88404G2.conditions22
  · exact RunNumericChecks88404G2.conditions23
  · exact RunNumericChecks88404G2.conditions24
  · exact RunNumericChecks88404G2.conditions25
  · exact RunNumericChecks88404G2.conditions26
  · exact RunNumericChecks88404G2.conditions27
  · exact RunNumericChecks88404G2.conditions28
  · exact RunNumericChecks88404G2.conditions29
  · exact RunNumericChecks88404G2.conditions30
  · exact RunNumericChecks88404G2.conditions31
  · exact RunNumericChecks88404G2.conditions32
  · exact RunNumericChecks88404G2.conditions33
  · exact RunNumericChecks88404G2.conditions34
  · exact RunNumericChecks88404G2.conditions35
  · exact RunNumericChecks88404G3.conditions36
  · exact RunNumericChecks88404G3.conditions37
  · exact RunNumericChecks88404G3.conditions38
  · exact RunNumericChecks88404G3.conditions39
  · exact RunNumericChecks88404G3.conditions40
  · exact RunNumericChecks88404G3.conditions41
  · exact RunNumericChecks88404G3.conditions42
  · exact RunNumericChecks88404G3.conditions43
  · exact RunNumericChecks88404G3.conditions44
  · exact RunNumericChecks88404G3.conditions45
  · exact RunNumericChecks88404G3.conditions46
  · exact RunNumericChecks88404G3.conditions47
  · exact RunNumericChecks88404G3.conditions48
  · exact RunNumericChecks88404G3.conditions49
  · exact RunNumericChecks88404G3.conditions50
  · exact RunNumericChecks88404G3.conditions51
  · exact RunNumericChecks88404G4.conditions52
  · exact RunNumericChecks88404G4.conditions53
  · exact RunNumericChecks88404G4.conditions54
  · exact RunNumericChecks88404G4.conditions55
  · exact RunNumericChecks88404G4.conditions56
  · exact RunNumericChecks88404G4.conditions57
  · exact RunNumericChecks88404G4.conditions58
  · exact RunNumericChecks88404G4.conditions59
  · exact RunNumericChecks88404G4.conditions60
  · exact RunNumericChecks88404G4.conditions61
  · exact RunNumericChecks88404G4.conditions62
  · exact RunNumericChecks88404G4.conditions63
  · exact RunNumericChecks88404G4.conditions64
  · exact RunNumericChecks88404G4.conditions65
  · exact RunNumericChecks88404G4.conditions66
  · exact RunNumericChecks88404G4.conditions67
  · exact RunNumericChecks88404G5.conditions68
  · exact RunNumericChecks88404G5.conditions69
  · exact RunNumericChecks88404G5.conditions70
  · exact RunNumericChecks88404G5.conditions71
  · exact RunNumericChecks88404G5.conditions72
  · exact RunNumericChecks88404G5.conditions73
  · exact RunNumericChecks88404G5.conditions74

#print axioms conditions
end JSP233.RunFacts88404
