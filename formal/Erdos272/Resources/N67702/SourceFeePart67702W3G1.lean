module

public import Erdos272.Resources.N67702.SourceFeeLeaf67702W3G1A
public import Erdos272.Resources.N67702.SourceFeeLeaf67702W3G1B

@[expose] public section

namespace JSP233.SourcePayment67702W3
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W3
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem weighted_blocks (N offset a b : ℕ) :
    6*G*(∑ i ∈ Finset.range (a+b),
      (Psi (offset+i+1)-Psi (offset+i))*Cost N (offset+i))=
    6*G*(∑ i ∈ Finset.range a,
      (Psi (offset+i+1)-Psi (offset+i))*Cost N (offset+i))+
    6*G*(∑ i ∈ Finset.range b,
      (Psi (offset+a+i+1)-Psi (offset+a+i))*Cost N (offset+a+i)) := by
  rw [Finset.sum_range_add]
  simp only [Nat.add_assoc]
  ring
#print axioms weighted_blocks

theorem fee_part1 (N : ℕ) : FeePart1 N=(24830060905813/5886125000000000 : ℝ)*(N : ℝ)^2+(3281288793890202013/164811500000000000 : ℝ)*N+(315183672925/6727 : ℝ) := by
  have hs : FeePart1 N=FeeLeaf1A N+FeeLeaf1B N := by
    exact weighted_blocks N 8 4 4
  rw [hs,fee_leaf1A,fee_leaf1B]
  norm_num
  ring
#print axioms fee_part1

end
end JSP233.SourcePayment67702W3
