module

public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericPlans86412

@[expose] public section

namespace JSP233.StrictRunPlans86412
set_option autoImplicit false

def plan (k : ℕ) : StrictRunSource86412.Plan :=
  RunNumericBridge88404.toPlan (StrictRunNumericPlans86412.plan k)

end JSP233.StrictRunPlans86412
