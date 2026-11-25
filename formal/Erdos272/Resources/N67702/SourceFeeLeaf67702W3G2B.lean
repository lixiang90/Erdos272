module

public import Erdos272.Arithmetic.N67702.SourceFeeData67702W3

@[expose] public section

namespace JSP233.SourcePayment67702W3
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W3
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def FeeLeaf2B (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 4, (Psi (20+i+1)-Psi (20+i))*Cost N (20+i))

theorem fee_leaf2B (N : ℕ) : FeeLeaf2B N=(1129375449777/480500000000000 : ℝ)*(N : ℝ)^2+(26333973090552807/1681750000000000 : ℝ)*N+(2129783130816/47089 : ℝ) := by
  simp only [FeeLeaf2B,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num [G,Psi,potential,Cost,Layer67702.Upper,WitnessActualLayer80470.Upper,WitnessHighNumeric67702.data,CleanupRows67702.data,WitnessHighNumeric67702.data082, WitnessHighNumeric67702.data083, WitnessHighNumeric67702.data084, WitnessHighNumeric67702.data085, WitnessHighNumeric67702.data086, CleanupRows67702.data82, CleanupRows67702.data83, CleanupRows67702.data84, CleanupRows67702.data85, CleanupRows67702.data86]
  ring
#print axioms fee_leaf2B

end
end JSP233.SourcePayment67702W3
