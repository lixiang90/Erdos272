module

public import Erdos272.Arithmetic.N88404.RunNumericBridge88404
public import Erdos272.Arithmetic.N86412.RunNumericPlans86412

@[expose] public section

namespace JSP233.RunPlans86412
set_option autoImplicit false

def plan (k : ℕ) : RunSource109474.Plan :=
  RunNumericBridge88404.toPlan (RunNumericPlans86412.plan k)

end JSP233.RunPlans86412
