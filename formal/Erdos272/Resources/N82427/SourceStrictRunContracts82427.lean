module

public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.StrictRunSource86412
public import Erdos272.Counting.N82427.StrictRunFacts82427
public import Erdos272.Arithmetic.N82427.SourceStrictRunFloors82427

@[expose] public section

namespace JSP233.SourceStrictRunContracts82427
open SourceContract86412
noncomputable section
set_option autoImplicit false

def run (i : ℕ) (hi : i < 38) : CertifiedContract where
  contract := ⟨(StrictRunPlans82427.plan i).lower, (StrictRunPlans82427.plan i).defect,
    (StrictRunPlans82427.plan i).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunSource86412.actual_run_plan_source (StrictRunPlans82427.plan i)
      (StrictRunFacts82427.conditions hi) (SourceStrictRunFloors82427.floors hi)
      hN hground hS hsize hdefect

end
end JSP233.SourceStrictRunContracts82427
