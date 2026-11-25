module

public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.StrictRunSource86412
public import Erdos272.Counting.N84364.StrictRunFacts84364
public import Erdos272.Arithmetic.N84364.SourceStrictRunFloors84364

@[expose] public section

namespace JSP233.SourceStrictRunContracts84364
open SourceContract86412
noncomputable section
set_option autoImplicit false

def run (i : ℕ) (hi : i < 24) : CertifiedContract where
  contract := ⟨(StrictRunPlans84364.plan i).lower, (StrictRunPlans84364.plan i).defect,
    (StrictRunPlans84364.plan i).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunSource86412.actual_run_plan_source (StrictRunPlans84364.plan i)
      (StrictRunFacts84364.conditions hi) (SourceStrictRunFloors84364.floors hi)
      hN hground hS hsize hdefect

end
end JSP233.SourceStrictRunContracts84364
