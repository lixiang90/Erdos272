module

public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209

@[expose] public section
namespace JSP233.FullPrefix209_000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem checked_part_0 : DualFrontier209.checkFrom FactorFullCertificate209.phi 0 8192 0 0 4980500294525256 20401609 = true := by
  decide +kernel
#print axioms checked_part_0
theorem checked_part_8192 : DualFrontier209.checkFrom FactorFullCertificate209.phi 8192 8192 4980500294525256 20401609 9960567334217735 81599337 = true := by
  decide +kernel
#print axioms checked_part_8192
theorem checked_part_16384 : DualFrontier209.checkFrom FactorFullCertificate209.phi 16384 8192 9960567334217735 81599337 14940585030365809 183591975 = true := by
  decide +kernel
#print axioms checked_part_16384
theorem checked_part_24576 : DualFrontier209.checkFrom FactorFullCertificate209.phi 24576 8192 14940585030365809 183591975 19920829981196116 326387383 = true := by
  decide +kernel
#print axioms checked_part_24576
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 0 32768 0 0 19920829981196116 326387383 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 0 0 0 4980500294525256 20401609 24576 19920829981196116 326387383 checked_part_0 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 8192 4980500294525256 20401609 9960567334217735 81599337 16384 19920829981196116 326387383 checked_part_8192 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 16384 9960567334217735 81599337 14940585030365809 183591975 8192 19920829981196116 326387383 checked_part_16384 checked_part_24576)))
theorem block_sound :
    (19920829981196116 = FrontierCheck209.massFloor FactorFullCertificate209.phi 32768 ∧
     326387383 = FrontierCheck209.triangle FactorFullCertificate209.phi 32768) ∧
    ∀ t, 0 < t → t ≤ 32768 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 0 0 0 19920829981196116 326387383 rfl rfl checked
theorem endpoint :
    19920829981196116 = FrontierCheck209.massFloor FactorFullCertificate209.phi 32768 ∧
    326387383 = FrontierCheck209.triangle FactorFullCertificate209.phi 32768 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 32768) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_000
