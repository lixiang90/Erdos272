import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_001
namespace JSP233.FullPrefix209_002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem checked_part_65536 : DualFrontier209.checkFrom FactorFullCertificate209.phi 65536 8192 39841132164060467 1305514925 44821474991186533 1652307173 = true := by
  decide +kernel
#print axioms checked_part_65536
theorem checked_part_73728 : DualFrontier209.checkFrom FactorFullCertificate209.phi 73728 8192 44821474991186533 1652307173 49801730836060978 2039892933 = true := by
  decide +kernel
#print axioms checked_part_73728
theorem checked_part_81920 : DualFrontier209.checkFrom FactorFullCertificate209.phi 81920 8192 49801730836060978 2039892933 54781667378838676 2468249133 = true := by
  decide +kernel
#print axioms checked_part_81920
theorem checked_part_90112 : DualFrontier209.checkFrom FactorFullCertificate209.phi 90112 8192 54781667378838676 2468249133 59761899437122899 2937428361 = true := by
  decide +kernel
#print axioms checked_part_90112
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 65536 32768 39841132164060467 1305514925 59761899437122899 2937428361 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 65536 39841132164060467 1305514925 44821474991186533 1652307173 24576 59761899437122899 2937428361 checked_part_65536 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 73728 44821474991186533 1652307173 49801730836060978 2039892933 16384 59761899437122899 2937428361 checked_part_73728 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 81920 49801730836060978 2039892933 54781667378838676 2468249133 8192 59761899437122899 2937428361 checked_part_81920 checked_part_90112)))
theorem block_sound :
    (59761899437122899 = FrontierCheck209.massFloor FactorFullCertificate209.phi 98304 ∧
     2937428361 = FrontierCheck209.triangle FactorFullCertificate209.phi 98304) ∧
    ∀ t, 65536 < t → t ≤ 98304 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 65536 39841132164060467 1305514925 59761899437122899 2937428361 FullPrefix209_001.endpoint.1 FullPrefix209_001.endpoint.2 checked
theorem endpoint :
    59761899437122899 = FrontierCheck209.massFloor FactorFullCertificate209.phi 98304 ∧
    2937428361 = FrontierCheck209.triangle FactorFullCertificate209.phi 98304 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 98304) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 65536
  · exact FullPrefix209_001.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_002
