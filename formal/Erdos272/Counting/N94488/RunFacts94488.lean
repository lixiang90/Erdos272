module

public import Erdos272.Arithmetic.N94488.RunChecks94488G0
public import Erdos272.Arithmetic.N94488.RunChecks94488G1
public import Erdos272.Arithmetic.N94488.RunChecks94488G2
public import Erdos272.Arithmetic.N94488.RunChecks94488G3
public import Erdos272.Arithmetic.N94488.RunChecks94488G4
public import Erdos272.Arithmetic.N94488.RunChecks94488G5
public import Erdos272.Arithmetic.N94488.RunChecks94488G6
public import Erdos272.Arithmetic.N94488.RunChecks94488G7
public import Erdos272.Arithmetic.N94488.RunChecks94488G8
public import Erdos272.Arithmetic.N94488.RunChecks94488G9
public import Erdos272.Arithmetic.N94488.RunChecks94488G10
public import Erdos272.Arithmetic.N94488.RunChecks94488G11
public import Erdos272.Arithmetic.N94488.RunChecks94488G12
public import Erdos272.Arithmetic.N94488.RunChecks94488G13
public import Erdos272.Arithmetic.N94488.RunChecks94488G14
public import Erdos272.Arithmetic.N94488.RunChecks94488G15
public import Erdos272.Arithmetic.N94488.RunChecks94488G16
public import Erdos272.Arithmetic.N94488.RunChecks94488G17

@[expose] public section

namespace JSP233.RunFacts94488
open RunSource109474 RunPlans94488
set_option autoImplicit false

theorem conditions {k : ℕ} (hk : k < 70) : Conditions (plan k) := by
  interval_cases k
  · exact RunChecks94488G0.conditions00
  · exact RunChecks94488G0.conditions01
  · exact RunChecks94488G0.conditions02
  · exact RunChecks94488G0.conditions03
  · exact RunChecks94488G1.conditions04
  · exact RunChecks94488G1.conditions05
  · exact RunChecks94488G1.conditions06
  · exact RunChecks94488G1.conditions07
  · exact RunChecks94488G2.conditions08
  · exact RunChecks94488G2.conditions09
  · exact RunChecks94488G2.conditions10
  · exact RunChecks94488G2.conditions11
  · exact RunChecks94488G3.conditions12
  · exact RunChecks94488G3.conditions13
  · exact RunChecks94488G3.conditions14
  · exact RunChecks94488G3.conditions15
  · exact RunChecks94488G4.conditions16
  · exact RunChecks94488G4.conditions17
  · exact RunChecks94488G4.conditions18
  · exact RunChecks94488G4.conditions19
  · exact RunChecks94488G5.conditions20
  · exact RunChecks94488G5.conditions21
  · exact RunChecks94488G5.conditions22
  · exact RunChecks94488G5.conditions23
  · exact RunChecks94488G6.conditions24
  · exact RunChecks94488G6.conditions25
  · exact RunChecks94488G6.conditions26
  · exact RunChecks94488G6.conditions27
  · exact RunChecks94488G7.conditions28
  · exact RunChecks94488G7.conditions29
  · exact RunChecks94488G7.conditions30
  · exact RunChecks94488G7.conditions31
  · exact RunChecks94488G8.conditions32
  · exact RunChecks94488G8.conditions33
  · exact RunChecks94488G8.conditions34
  · exact RunChecks94488G8.conditions35
  · exact RunChecks94488G9.conditions36
  · exact RunChecks94488G9.conditions37
  · exact RunChecks94488G9.conditions38
  · exact RunChecks94488G9.conditions39
  · exact RunChecks94488G10.conditions40
  · exact RunChecks94488G10.conditions41
  · exact RunChecks94488G10.conditions42
  · exact RunChecks94488G10.conditions43
  · exact RunChecks94488G11.conditions44
  · exact RunChecks94488G11.conditions45
  · exact RunChecks94488G11.conditions46
  · exact RunChecks94488G11.conditions47
  · exact RunChecks94488G12.conditions48
  · exact RunChecks94488G12.conditions49
  · exact RunChecks94488G12.conditions50
  · exact RunChecks94488G12.conditions51
  · exact RunChecks94488G13.conditions52
  · exact RunChecks94488G13.conditions53
  · exact RunChecks94488G13.conditions54
  · exact RunChecks94488G13.conditions55
  · exact RunChecks94488G14.conditions56
  · exact RunChecks94488G14.conditions57
  · exact RunChecks94488G14.conditions58
  · exact RunChecks94488G14.conditions59
  · exact RunChecks94488G15.conditions60
  · exact RunChecks94488G15.conditions61
  · exact RunChecks94488G15.conditions62
  · exact RunChecks94488G15.conditions63
  · exact RunChecks94488G16.conditions64
  · exact RunChecks94488G16.conditions65
  · exact RunChecks94488G16.conditions66
  · exact RunChecks94488G16.conditions67
  · exact RunChecks94488G17.conditions68
  · exact RunChecks94488G17.conditions69

#print axioms conditions
end JSP233.RunFacts94488
