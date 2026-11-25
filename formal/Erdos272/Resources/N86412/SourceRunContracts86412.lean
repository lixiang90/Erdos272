module

public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Counting.N86412.RunFacts86412
public import Erdos272.Arithmetic.N86412.SourceRunFloors86412

@[expose] public section

namespace JSP233.SourceRunContracts86412
open SourceContract86412
noncomputable section
set_option autoImplicit false

def run (i : ℕ) (hi : i < 21) : CertifiedContract where
  contract := ⟨(RunPlans86412.plan i).lower, (RunPlans86412.plan i).defect,
    (RunPlans86412.plan i).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact RunSource109474.actual_run_plan_source (RunPlans86412.plan i)
      (RunFacts86412.conditions hi) (SourceRunFloors86412.floors hi)
      hN hground hS hsize hdefect

end
end JSP233.SourceRunContracts86412
