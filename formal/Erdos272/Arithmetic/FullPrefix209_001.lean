import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_000
namespace JSP233.FullPrefix209_001
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem checked_part_32768 : DualFrontier209.checkFrom FactorFullCertificate209.phi 32768 8192 19920829981196116 326387383 24900790139503646 509970149 = true := by
  decide +kernel
#print axioms checked_part_32768
theorem checked_part_40960 : DualFrontier209.checkFrom FactorFullCertificate209.phi 40960 8192 24900790139503646 509970149 29881027498944783 734360915 = true := by
  decide +kernel
#print axioms checked_part_40960
theorem checked_part_49152 : DualFrontier209.checkFrom FactorFullCertificate209.phi 49152 8192 29881027498944783 734360915 34861202736486210 999547035 = true := by
  decide +kernel
#print axioms checked_part_49152
theorem checked_part_57344 : DualFrontier209.checkFrom FactorFullCertificate209.phi 57344 8192 34861202736486210 999547035 39841132164060467 1305514925 = true := by
  decide +kernel
#print axioms checked_part_57344
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 32768 32768 19920829981196116 326387383 39841132164060467 1305514925 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 32768 19920829981196116 326387383 24900790139503646 509970149 24576 39841132164060467 1305514925 checked_part_32768 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 40960 24900790139503646 509970149 29881027498944783 734360915 16384 39841132164060467 1305514925 checked_part_40960 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 49152 29881027498944783 734360915 34861202736486210 999547035 8192 39841132164060467 1305514925 checked_part_49152 checked_part_57344)))
theorem block_sound :
    (39841132164060467 = FrontierCheck209.massFloor FactorFullCertificate209.phi 65536 ∧
     1305514925 = FrontierCheck209.triangle FactorFullCertificate209.phi 65536) ∧
    ∀ t, 32768 < t → t ≤ 65536 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 32768 19920829981196116 326387383 39841132164060467 1305514925 FullPrefix209_000.endpoint.1 FullPrefix209_000.endpoint.2 checked
theorem endpoint :
    39841132164060467 = FrontierCheck209.massFloor FactorFullCertificate209.phi 65536 ∧
    1305514925 = FrontierCheck209.triangle FactorFullCertificate209.phi 65536 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 65536) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 32768
  · exact FullPrefix209_000.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_001
