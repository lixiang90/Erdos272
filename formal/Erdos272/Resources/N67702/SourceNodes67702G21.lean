module

public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N80470.SourceNodes80470G3
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N67702.UniformChecks67702G2

@[expose] public section

namespace JSP233.SourceNodes67702G21
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node336 : CertifiedContract := SourceNodes80470G3.node054

def node337 : CertifiedContract := ⟨⟨101,1,3042⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks67702G2.checked337
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

end
end JSP233.SourceNodes67702G21
