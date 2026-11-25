module

public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.StrictRunSource86412
public import Erdos272.Counting.N86412.StrictRunFacts86412
public import Erdos272.Arithmetic.N86412.SourceStrictRunFloors86412

@[expose] public section

namespace JSP233.SourceStrictRunContracts86412
open SourceContract86412
noncomputable section
set_option autoImplicit false

def run (i : ℕ) (hi : i < 16) : CertifiedContract where
  contract := ⟨(StrictRunPlans86412.plan i).lower, (StrictRunPlans86412.plan i).defect,
    (StrictRunPlans86412.plan i).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunSource86412.actual_run_plan_source (StrictRunPlans86412.plan i)
      (StrictRunFacts86412.conditions hi) (SourceStrictRunFloors86412.floors hi)
      hN hground hS hsize hdefect

end
end JSP233.SourceStrictRunContracts86412
