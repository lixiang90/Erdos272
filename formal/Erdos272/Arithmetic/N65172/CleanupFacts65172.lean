module

public import Erdos272.Arithmetic.N65172.CleanupFacts65172G0
public import Erdos272.Arithmetic.N65172.CleanupFacts65172G1
public import Erdos272.Arithmetic.N65172.CleanupFacts65172G2

@[expose] public section

namespace JSP233.CleanupFacts65172
open CleanupRows65172
open CleanupEval208 (ChunkFacts)
open CleanupMachineSound208 (toRow toTotals)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem all_facts {k : ℕ} (hk : k<43) : ChunkFacts (toRow (data k).row) 1 (data k).steps (toTotals (data k).total) := by
  interval_cases k
  · exact CleanupFacts65172G0.fact00
  · exact CleanupFacts65172G0.fact01
  · exact CleanupFacts65172G0.fact02
  · exact CleanupFacts65172G0.fact03
  · exact CleanupFacts65172G0.fact04
  · exact CleanupFacts65172G0.fact05
  · exact CleanupFacts65172G0.fact06
  · exact CleanupFacts65172G0.fact07
  · exact CleanupFacts65172G0.fact08
  · exact CleanupFacts65172G0.fact09
  · exact CleanupFacts65172G0.fact10
  · exact CleanupFacts65172G0.fact11
  · exact CleanupFacts65172G0.fact12
  · exact CleanupFacts65172G0.fact13
  · exact CleanupFacts65172G0.fact14
  · exact CleanupFacts65172G0.fact15
  · exact CleanupFacts65172G1.fact16
  · exact CleanupFacts65172G1.fact17
  · exact CleanupFacts65172G1.fact18
  · exact CleanupFacts65172G1.fact19
  · exact CleanupFacts65172G1.fact20
  · exact CleanupFacts65172G1.fact21
  · exact CleanupFacts65172G1.fact22
  · exact CleanupFacts65172G1.fact23
  · exact CleanupFacts65172G1.fact24
  · exact CleanupFacts65172G1.fact25
  · exact CleanupFacts65172G1.fact26
  · exact CleanupFacts65172G1.fact27
  · exact CleanupFacts65172G1.fact28
  · exact CleanupFacts65172G1.fact29
  · exact CleanupFacts65172G1.fact30
  · exact CleanupFacts65172G1.fact31
  · exact CleanupFacts65172G2.fact32
  · exact CleanupFacts65172G2.fact33
  · exact CleanupFacts65172G2.fact34
  · exact CleanupFacts65172G2.fact35
  · exact CleanupFacts65172G2.fact36
  · exact CleanupFacts65172G2.fact37
  · exact CleanupFacts65172G2.fact38
  · exact CleanupFacts65172G2.fact39
  · exact CleanupFacts65172G2.fact40
  · exact CleanupFacts65172G2.fact41
  · exact CleanupFacts65172G2.fact42

#print axioms all_facts
end
end JSP233.CleanupFacts65172
