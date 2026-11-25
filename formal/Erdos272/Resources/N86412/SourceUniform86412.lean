module

public import Erdos272.Counting.N86412.UniformSound86412
public import Erdos272.Counting.N86412.UniformFacts86412
public import Erdos272.Counting.N86412.StrictPool86412

@[expose] public section

namespace JSP233.SourceUniform86412
open SourceContract86412
noncomputable section
set_option autoImplicit false

def uniform (i : ℕ) (hi : i < 54) : CertifiedContract where
  contract := ⟨(UniformPlans86412.plan i).lower, 1, (UniformPlans86412.plan i).target⟩
  actual := UniformSound86412.uniform_paid
    (UniformFacts86412.sizes hi).1 (UniformFacts86412.sizes hi).2 (UniformFacts86412.bound hi)
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)

end
end JSP233.SourceUniform86412
