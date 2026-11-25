module

public import Erdos272.Resources.N67702.SourceFeePart67702W3G0
public import Erdos272.Resources.N67702.SourceFeePart67702W3G1
public import Erdos272.Resources.N67702.SourceFeePart67702W3G2
public import Erdos272.Resources.N67702.SourceFeePart67702W3G3

@[expose] public section

namespace JSP233.SourcePayment67702W3
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W3
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem sum_blocks (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range 33, f i)=
      (∑ i ∈ Finset.range 8, f i)+(∑ i ∈ Finset.range 8, f (8+i))+
      (∑ i ∈ Finset.range 8, f (16+i))+(∑ i ∈ Finset.range 9, f (24+i)) := by
  calc
    _=(∑ i ∈ Finset.range 24, f i)+(∑ i ∈ Finset.range 9, f (24+i)) :=
      Finset.sum_range_add f 24 9
    _=((∑ i ∈ Finset.range 16, f i)+(∑ i ∈ Finset.range 8, f (16+i)))+
        (∑ i ∈ Finset.range 9, f (24+i)) := by rw [Finset.sum_range_add f 16 8]
    _=_ := by rw [Finset.sum_range_add f 8 8]
#print axioms sum_blocks

theorem fee (N : ℕ) : Weighted N=SourceUpper N := by
  have hs : Weighted N=FeePart0 N+FeePart1 N+FeePart2 N+FeePart3 N := by
    simp only [Weighted,FeePart0,FeePart1,FeePart2,FeePart3,Nat.zero_add]
    rw [sum_blocks]
    ring
  rw [hs,fee_part0,fee_part1,fee_part2,fee_part3]
  norm_num [SourceUpper,CoeffA,CoeffB,CoeffC]
  ring
#print axioms fee
end
end JSP233.SourcePayment67702W3
