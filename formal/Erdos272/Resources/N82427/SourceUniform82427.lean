module

public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Counting.N82427.UniformFacts82427
public import Erdos272.Counting.N86412.StrictPool86412

@[expose] public section

namespace JSP233.SourceUniform82427
open SourceContract86412
noncomputable section
set_option autoImplicit false

def uniform (i : ℕ) (hi : i < 40) : CertifiedContract where
  contract := ⟨(UniformPlans82427.plan i).lower, 1, (UniformPlans82427.plan i).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact UniformBridge84364.uniform_paid
      (UniformFacts82427.sizes hi).1 (UniformFacts82427.sizes hi).2 (UniformFacts82427.bound hi)
      (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)
      hN hground hS hsize hdefect

end
end JSP233.SourceUniform82427
