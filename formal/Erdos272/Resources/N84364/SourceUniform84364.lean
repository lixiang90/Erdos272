module

public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Counting.N84364.UniformFacts84364
public import Erdos272.Counting.N86412.StrictPool86412

@[expose] public section

namespace JSP233.SourceUniform84364
open SourceContract86412
noncomputable section
set_option autoImplicit false

def uniform (i : ℕ) (hi : i < 23) : CertifiedContract where
  contract := ⟨(UniformPlans84364.plan i).lower, 1, (UniformPlans84364.plan i).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact UniformBridge84364.uniform_paid
      (UniformFacts84364.sizes hi).1 (UniformFacts84364.sizes hi).2 (UniformFacts84364.bound hi)
      (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)
      hN hground hS hsize hdefect

end
end JSP233.SourceUniform84364
