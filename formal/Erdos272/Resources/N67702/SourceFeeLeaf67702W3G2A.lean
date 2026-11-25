module

public import Erdos272.Arithmetic.N67702.SourceFeeData67702W3

@[expose] public section

namespace JSP233.SourcePayment67702W3
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W3
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def FeeLeaf2A (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 4, (Psi (16+i+1)-Psi (16+i))*Cost N (16+i))

theorem fee_leaf2A (N : ℕ) : FeeLeaf2A N=(42228007546167/23544500000000000 : ℝ)*(N : ℝ)^2+(256165794917940903/23544500000000000 : ℝ)*N+(1329707865272/47089 : ℝ) := by
  simp only [FeeLeaf2A,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num [G,Psi,potential,Cost,Layer67702.Upper,WitnessActualLayer80470.Upper,WitnessHighNumeric67702.data,CleanupRows67702.data,WitnessHighNumeric67702.data078, WitnessHighNumeric67702.data079, WitnessHighNumeric67702.data080, WitnessHighNumeric67702.data081, WitnessHighNumeric67702.data082, CleanupRows67702.data78, CleanupRows67702.data79, CleanupRows67702.data80, CleanupRows67702.data81, CleanupRows67702.data82]
  ring
#print axioms fee_leaf2A

end
end JSP233.SourcePayment67702W3
