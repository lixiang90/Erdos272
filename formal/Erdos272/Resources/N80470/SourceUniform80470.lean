module

public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Counting.N80470.UniformFacts80470
public import Erdos272.Counting.N86412.StrictPool86412

@[expose] public section

namespace JSP233.SourceUniform80470
open SourceContract86412
noncomputable section
set_option autoImplicit false

def uniform (i : ℕ) (hi : i < 5) : CertifiedContract where
  contract := ⟨(UniformPlans80470.plan i).lower, 1, (UniformPlans80470.plan i).target⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact UniformBridge84364.uniform_paid
      (UniformFacts80470.sizes hi).1 (UniformFacts80470.sizes hi).2 (UniformFacts80470.bound hi)
      (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)
      hN hground hS hsize hdefect

end
end JSP233.SourceUniform80470
