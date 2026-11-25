module

public import Erdos272.Arithmetic.N67702.SourceFeeData67702W3

@[expose] public section

namespace JSP233.SourcePayment67702W3
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W3
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def FeeLeaf1A (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 4, (Psi (8+i+1)-Psi (8+i))*Cost N (8+i))

theorem fee_leaf1A (N : ℕ) : FeeLeaf1A N=(9270120239913/5886125000000000 : ℝ)*(N : ℝ)^2+(22731680427017617/4708900000000000 : ℝ)*N+(543701107895/47089 : ℝ) := by
  simp only [FeeLeaf1A,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num [G,Psi,potential,Cost,Layer67702.Upper,WitnessActualLayer80470.Upper,WitnessHighNumeric67702.data,CleanupRows67702.data,WitnessHighNumeric67702.data070, WitnessHighNumeric67702.data071, WitnessHighNumeric67702.data072, WitnessHighNumeric67702.data073, WitnessHighNumeric67702.data074, CleanupRows67702.data70, CleanupRows67702.data71, CleanupRows67702.data72, CleanupRows67702.data73, CleanupRows67702.data74]
  ring
#print axioms fee_leaf1A

end
end JSP233.SourcePayment67702W3
