module

public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Arithmetic.N84364.StrictRunNumericPlans84364

@[expose] public section

namespace JSP233.StrictRunPlans84364
set_option autoImplicit false

def plan (k : ℕ) : StrictRunSource86412.Plan :=
  RunNumericBridge88404.toPlan (StrictRunNumericPlans84364.plan k)

end JSP233.StrictRunPlans84364
