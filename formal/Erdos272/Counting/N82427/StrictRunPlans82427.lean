module

public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Arithmetic.N82427.StrictRunNumericPlans82427

@[expose] public section

namespace JSP233.StrictRunPlans82427
set_option autoImplicit false

def plan (k : ℕ) : StrictRunSource86412.Plan :=
  RunNumericBridge88404.toPlan (StrictRunNumericPlans82427.plan k)

end JSP233.StrictRunPlans82427
