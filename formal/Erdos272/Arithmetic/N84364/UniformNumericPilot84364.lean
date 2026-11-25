module

public import Erdos272.Arithmetic.N84364.UniformNumeric84364

@[expose] public section

namespace JSP233.UniformNumericPilot84364
open UniformNumeric84364
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def plan0 : Plan := ⟨88,2280⟩
theorem checked0 : plan0.target ≤ value plan0.lower := by decide +kernel
#print axioms checked0

def plan1 : Plan := ⟨121,4310⟩
theorem checked1 : plan1.target ≤ value plan1.lower := by decide +kernel
#print axioms checked1

def plan2 : Plan := ⟨167,8360⟩
theorem checked2 : plan2.target ≤ value plan2.lower := by decide +kernel
#print axioms checked2

def plan3 : Plan := ⟨198,11706⟩
theorem checked3 : plan3.target ≤ value plan3.lower := by decide +kernel
#print axioms checked3

end JSP233.UniformNumericPilot84364
