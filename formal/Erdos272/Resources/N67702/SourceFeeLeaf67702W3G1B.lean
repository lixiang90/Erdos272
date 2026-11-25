module

public import Erdos272.Arithmetic.N67702.SourceFeeData67702W3

@[expose] public section

namespace JSP233.SourcePayment67702W3
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W3
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def FeeLeaf1B (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 4, (Psi (12+i+1)-Psi (12+i))*Cost N (12+i))

theorem fee_leaf1B (N : ℕ) : FeeLeaf1B N=(155599406659/58861250000000 : ℝ)*(N : ℝ)^2+(1242839989472292709/82405750000000000 : ℝ)*N+(1662584602580/47089 : ℝ) := by
  simp only [FeeLeaf1B,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num [G,Psi,potential,Cost,Layer67702.Upper,WitnessActualLayer80470.Upper,WitnessHighNumeric67702.data,CleanupRows67702.data,WitnessHighNumeric67702.data074, WitnessHighNumeric67702.data075, WitnessHighNumeric67702.data076, WitnessHighNumeric67702.data077, WitnessHighNumeric67702.data078, CleanupRows67702.data74, CleanupRows67702.data75, CleanupRows67702.data76, CleanupRows67702.data77, CleanupRows67702.data78]
  ring
#print axioms fee_leaf1B

end
end JSP233.SourcePayment67702W3
