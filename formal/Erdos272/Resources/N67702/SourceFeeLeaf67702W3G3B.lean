module

public import Erdos272.Arithmetic.N67702.SourceFeeData67702W3

@[expose] public section

namespace JSP233.SourcePayment67702W3
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W3
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def FeeLeaf3B (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 5, (Psi (28+i+1)-Psi (28+i))*Cost N (28+i))

theorem fee_leaf3B (N : ℕ) : FeeLeaf3B N=(32025868933601/11772250000000000 : ℝ)*(N : ℝ)^2+(765317863821796951/32962300000000000 : ℝ)*N+(544814110576/6727 : ℝ) := by
  simp only [FeeLeaf3B,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num [G,Psi,potential,Cost,Layer67702.Upper,WitnessActualLayer80470.Upper,WitnessHighNumeric67702.data,CleanupRows67702.data,WitnessHighNumeric67702.data090, WitnessHighNumeric67702.data091, WitnessHighNumeric67702.data092, WitnessHighNumeric67702.data093, WitnessHighNumeric67702.data094, WitnessHighNumeric67702.data095, CleanupRows67702.data90, CleanupRows67702.data91, CleanupRows67702.data92, CleanupRows67702.data93, CleanupRows67702.data94, CleanupRows67702.data95]
  ring
#print axioms fee_leaf3B

end
end JSP233.SourcePayment67702W3
