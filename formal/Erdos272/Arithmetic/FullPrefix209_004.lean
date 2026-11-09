module

public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_003

@[expose] public section
namespace JSP233.FullPrefix209_004
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem checked_part_131072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 131072 8192 79682615388525489 5222105723 84662647574790057 5895249507 = true := by
  decide +kernel
#print axioms checked_part_131072
theorem checked_part_139264 : DualFrontier209.checkFrom FactorFullCertificate209.phi 139264 8192 84662647574790057 5895249507 89642572226492894 6609172985 = true := by
  decide +kernel
#print axioms checked_part_139264
theorem checked_part_147456 : DualFrontier209.checkFrom FactorFullCertificate209.phi 147456 8192 89642572226492894 6609172985 94622925270026032 7363956923 = true := by
  decide +kernel
#print axioms checked_part_147456
theorem checked_part_155648 : DualFrontier209.checkFrom FactorFullCertificate209.phi 155648 8192 94622925270026032 7363956923 99602812934952487 8159465417 = true := by
  decide +kernel
#print axioms checked_part_155648
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 131072 32768 79682615388525489 5222105723 99602812934952487 8159465417 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 131072 79682615388525489 5222105723 84662647574790057 5895249507 24576 99602812934952487 8159465417 checked_part_131072 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 139264 84662647574790057 5895249507 89642572226492894 6609172985 16384 99602812934952487 8159465417 checked_part_139264 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 147456 89642572226492894 6609172985 94622925270026032 7363956923 8192 99602812934952487 8159465417 checked_part_147456 checked_part_155648)))
theorem block_sound :
    (99602812934952487 = FrontierCheck209.massFloor FactorFullCertificate209.phi 163840 ∧
     8159465417 = FrontierCheck209.triangle FactorFullCertificate209.phi 163840) ∧
    ∀ t, 131072 < t → t ≤ 163840 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 131072 79682615388525489 5222105723 99602812934952487 8159465417 FullPrefix209_003.endpoint.1 FullPrefix209_003.endpoint.2 checked
theorem endpoint :
    99602812934952487 = FrontierCheck209.massFloor FactorFullCertificate209.phi 163840 ∧
    8159465417 = FrontierCheck209.triangle FactorFullCertificate209.phi 163840 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 163840) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 131072
  · exact FullPrefix209_003.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_004
