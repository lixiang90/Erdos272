module

public import Erdos272.Arithmetic.N109474.RunChecks109474G0
public import Erdos272.Arithmetic.N109474.RunChecks109474G1
public import Erdos272.Arithmetic.N109474.RunChecks109474G2
public import Erdos272.Arithmetic.N109474.RunChecks109474G3
public import Erdos272.Arithmetic.N109474.RunChecks109474G4
public import Erdos272.Arithmetic.N109474.RunChecks109474G5
public import Erdos272.Arithmetic.N109474.RunChecks109474G6
public import Erdos272.Arithmetic.N109474.RunChecks109474G7
public import Erdos272.Arithmetic.N109474.RunChecks109474G8
public import Erdos272.Arithmetic.N109474.RunChecks109474G9
public import Erdos272.Arithmetic.N109474.RunChecks109474G10
public import Erdos272.Arithmetic.N109474.RunChecks109474G11
public import Erdos272.Arithmetic.N109474.RunChecks109474G12
public import Erdos272.Arithmetic.N109474.RunChecks109474G13
public import Erdos272.Arithmetic.N109474.RunChecks109474G14

@[expose] public section

namespace JSP233.RunFacts109474
open RunSource109474 RunPlans109474
set_option autoImplicit false

theorem conditions {k : ℕ} (hk : k < 60) : Conditions (plan k) := by
  interval_cases k
  · exact RunChecks109474G0.conditions00
  · exact RunChecks109474G0.conditions01
  · exact RunChecks109474G0.conditions02
  · exact RunChecks109474G0.conditions03
  · exact RunChecks109474G1.conditions04
  · exact RunChecks109474G1.conditions05
  · exact RunChecks109474G1.conditions06
  · exact RunChecks109474G1.conditions07
  · exact RunChecks109474G2.conditions08
  · exact RunChecks109474G2.conditions09
  · exact RunChecks109474G2.conditions10
  · exact RunChecks109474G2.conditions11
  · exact RunChecks109474G3.conditions12
  · exact RunChecks109474G3.conditions13
  · exact RunChecks109474G3.conditions14
  · exact RunChecks109474G3.conditions15
  · exact RunChecks109474G4.conditions16
  · exact RunChecks109474G4.conditions17
  · exact RunChecks109474G4.conditions18
  · exact RunChecks109474G4.conditions19
  · exact RunChecks109474G5.conditions20
  · exact RunChecks109474G5.conditions21
  · exact RunChecks109474G5.conditions22
  · exact RunChecks109474G5.conditions23
  · exact RunChecks109474G6.conditions24
  · exact RunChecks109474G6.conditions25
  · exact RunChecks109474G6.conditions26
  · exact RunChecks109474G6.conditions27
  · exact RunChecks109474G7.conditions28
  · exact RunChecks109474G7.conditions29
  · exact RunChecks109474G7.conditions30
  · exact RunChecks109474G7.conditions31
  · exact RunChecks109474G8.conditions32
  · exact RunChecks109474G8.conditions33
  · exact RunChecks109474G8.conditions34
  · exact RunChecks109474G8.conditions35
  · exact RunChecks109474G9.conditions36
  · exact RunChecks109474G9.conditions37
  · exact RunChecks109474G9.conditions38
  · exact RunChecks109474G9.conditions39
  · exact RunChecks109474G10.conditions40
  · exact RunChecks109474G10.conditions41
  · exact RunChecks109474G10.conditions42
  · exact RunChecks109474G10.conditions43
  · exact RunChecks109474G11.conditions44
  · exact RunChecks109474G11.conditions45
  · exact RunChecks109474G11.conditions46
  · exact RunChecks109474G11.conditions47
  · exact RunChecks109474G12.conditions48
  · exact RunChecks109474G12.conditions49
  · exact RunChecks109474G12.conditions50
  · exact RunChecks109474G12.conditions51
  · exact RunChecks109474G13.conditions52
  · exact RunChecks109474G13.conditions53
  · exact RunChecks109474G13.conditions54
  · exact RunChecks109474G13.conditions55
  · exact RunChecks109474G14.conditions56
  · exact RunChecks109474G14.conditions57
  · exact RunChecks109474G14.conditions58
  · exact RunChecks109474G14.conditions59

#print axioms conditions
end JSP233.RunFacts109474
