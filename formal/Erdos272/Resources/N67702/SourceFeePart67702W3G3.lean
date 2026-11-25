module

public import Erdos272.Resources.N67702.SourceFeeLeaf67702W3G3A
public import Erdos272.Resources.N67702.SourceFeeLeaf67702W3G3B
public import Erdos272.Resources.N67702.SourceFeePart67702W3G1

@[expose] public section

namespace JSP233.SourcePayment67702W3
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W3
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem fee_part3 (N : ℕ) : FeePart3 N=(12995059427089/2943062500000000 : ℝ)*(N : ℝ)^2+(5914513036931178319/164811500000000000 : ℝ)*N+(5686525709542/47089 : ℝ) := by
  have hs : FeePart3 N=FeeLeaf3A N+FeeLeaf3B N := by
    exact weighted_blocks N 24 4 5
  rw [hs,fee_leaf3A,fee_leaf3B]
  norm_num
  ring
#print axioms fee_part3

end
end JSP233.SourcePayment67702W3
