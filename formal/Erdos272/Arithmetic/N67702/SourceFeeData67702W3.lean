module

public import Erdos272.Resources.N67702.Layer67702
public import Erdos272.Resources.N67702.SourceData67702W3

@[expose] public section

namespace JSP233.SourcePayment67702W3
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W3
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Cost (N i : ℕ) : ℝ := if i=0 then 0 else Layer67702.Upper N (64+(i-1))
def Weighted (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 33, (Psi (i+1)-Psi i)*Cost N i)

def FeePart0 (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 8, (Psi (0+i+1)-Psi (0+i))*Cost N (0+i))

def FeePart1 (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 8, (Psi (8+i+1)-Psi (8+i))*Cost N (8+i))

def FeePart2 (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 8, (Psi (16+i+1)-Psi (16+i))*Cost N (16+i))

def FeePart3 (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 9, (Psi (24+i+1)-Psi (24+i))*Cost N (24+i))

end
end JSP233.SourcePayment67702W3
