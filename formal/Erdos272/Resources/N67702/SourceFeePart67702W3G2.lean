module

public import Erdos272.Resources.N67702.SourceFeeLeaf67702W3G2A
public import Erdos272.Resources.N67702.SourceFeeLeaf67702W3G2B
public import Erdos272.Resources.N67702.SourceFeePart67702W3G1

@[expose] public section

namespace JSP233.SourcePayment67702W3
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W3
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem fee_part2 (N : ℕ) : FeePart2 N=(2439185114631/588612500000000 : ℝ)*(N : ℝ)^2+(624841418185680201/23544500000000000 : ℝ)*N+(3459490996088/47089 : ℝ) := by
  have hs : FeePart2 N=FeeLeaf2A N+FeeLeaf2B N := by
    exact weighted_blocks N 16 4 4
  rw [hs,fee_leaf2A,fee_leaf2B]
  norm_num
  ring
#print axioms fee_part2

end
end JSP233.SourcePayment67702W3
