module

public import Erdos272.Arithmetic.N67702.SourceFeeData67702W3

@[expose] public section

namespace JSP233.SourcePayment67702W3
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W3
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def FeeLeaf3A (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 4, (Psi (24+i+1)-Psi (24+i))*Cost N (24+i))

theorem fee_leaf3A (N : ℕ) : FeeLeaf3A N=(3990873754951/2354450000000000 : ℝ)*(N : ℝ)^2+(521980929455548391/41202875000000000 : ℝ)*N+(1872826935510/47089 : ℝ) := by
  simp only [FeeLeaf3A,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num [G,Psi,potential,Cost,Layer67702.Upper,WitnessActualLayer80470.Upper,WitnessHighNumeric67702.data,CleanupRows67702.data,WitnessHighNumeric67702.data086, WitnessHighNumeric67702.data087, WitnessHighNumeric67702.data088, WitnessHighNumeric67702.data089, WitnessHighNumeric67702.data090, CleanupRows67702.data86, CleanupRows67702.data87, CleanupRows67702.data88, CleanupRows67702.data89, CleanupRows67702.data90]
  ring
#print axioms fee_leaf3A

end
end JSP233.SourcePayment67702W3
