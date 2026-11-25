module

public import Erdos272.Arithmetic.N88404.RunNumericBridge88404
public import Erdos272.Arithmetic.N88404.RunNumericPlans88404

@[expose] public section

namespace JSP233.RunPlans88404
set_option autoImplicit false

def plan (k : ℕ) : RunSource109474.Plan :=
  RunNumericBridge88404.toPlan (RunNumericPlans88404.plan k)

end JSP233.RunPlans88404
