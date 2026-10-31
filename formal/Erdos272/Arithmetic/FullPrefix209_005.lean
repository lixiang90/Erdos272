import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_004
namespace JSP233.FullPrefix209_005
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem checked_part_163840 : DualFrontier209.checkFrom FactorFullCertificate209.phi 163840 8192 99602812934952487 8159465417 104583021674014501 8995822349 = true := by
  decide +kernel
#print axioms checked_part_163840
theorem checked_part_172032 : DualFrontier209.checkFrom FactorFullCertificate209.phi 172032 8192 104583021674014501 8995822349 109563413320451763 9873010689 = true := by
  decide +kernel
#print axioms checked_part_172032
theorem checked_part_180224 : DualFrontier209.checkFrom FactorFullCertificate209.phi 180224 8192 109563413320451763 9873010689 114543332080862934 10790911353 = true := by
  decide +kernel
#print axioms checked_part_180224
theorem checked_part_188416 : DualFrontier209.checkFrom FactorFullCertificate209.phi 188416 8192 114543332080862934 10790911353 119523528010270651 11749660201 = true := by
  decide +kernel
#print axioms checked_part_188416
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 163840 32768 99602812934952487 8159465417 119523528010270651 11749660201 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 163840 99602812934952487 8159465417 104583021674014501 8995822349 24576 119523528010270651 11749660201 checked_part_163840 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 172032 104583021674014501 8995822349 109563413320451763 9873010689 16384 119523528010270651 11749660201 checked_part_172032 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 180224 109563413320451763 9873010689 114543332080862934 10790911353 8192 119523528010270651 11749660201 checked_part_180224 checked_part_188416)))
theorem block_sound :
    (119523528010270651 = FrontierCheck209.massFloor FactorFullCertificate209.phi 196608 ∧
     11749660201 = FrontierCheck209.triangle FactorFullCertificate209.phi 196608) ∧
    ∀ t, 163840 < t → t ≤ 196608 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 163840 99602812934952487 8159465417 119523528010270651 11749660201 FullPrefix209_004.endpoint.1 FullPrefix209_004.endpoint.2 checked
theorem endpoint :
    119523528010270651 = FrontierCheck209.massFloor FactorFullCertificate209.phi 196608 ∧
    11749660201 = FrontierCheck209.triangle FactorFullCertificate209.phi 196608 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 196608) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 163840
  · exact FullPrefix209_004.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_005
