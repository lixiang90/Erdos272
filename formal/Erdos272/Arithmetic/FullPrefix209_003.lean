import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_002
namespace JSP233.FullPrefix209_003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem checked_part_98304 : DualFrontier209.checkFrom FactorFullCertificate209.phi 98304 8192 59761899437122899 2937428361 64742029722000505 3447395577 = true := by
  decide +kernel
#print axioms checked_part_98304
theorem checked_part_106496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 106496 8192 64742029722000505 3447395577 69722044567745935 3998146719 = true := by
  decide +kernel
#print axioms checked_part_106496
theorem checked_part_114688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 114688 8192 69722044567745935 3998146719 74702216386621049 4589712419 = true := by
  decide +kernel
#print axioms checked_part_114688
theorem checked_part_122880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 122880 8192 74702216386621049 4589712419 79682615388525489 5222105723 = true := by
  decide +kernel
#print axioms checked_part_122880
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 98304 32768 59761899437122899 2937428361 79682615388525489 5222105723 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 98304 59761899437122899 2937428361 64742029722000505 3447395577 24576 79682615388525489 5222105723 checked_part_98304 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 106496 64742029722000505 3447395577 69722044567745935 3998146719 16384 79682615388525489 5222105723 checked_part_106496 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 114688 69722044567745935 3998146719 74702216386621049 4589712419 8192 79682615388525489 5222105723 checked_part_114688 checked_part_122880)))
theorem block_sound :
    (79682615388525489 = FrontierCheck209.massFloor FactorFullCertificate209.phi 131072 ∧
     5222105723 = FrontierCheck209.triangle FactorFullCertificate209.phi 131072) ∧
    ∀ t, 98304 < t → t ≤ 131072 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 98304 59761899437122899 2937428361 79682615388525489 5222105723 FullPrefix209_002.endpoint.1 FullPrefix209_002.endpoint.2 checked
theorem endpoint :
    79682615388525489 = FrontierCheck209.massFloor FactorFullCertificate209.phi 131072 ∧
    5222105723 = FrontierCheck209.triangle FactorFullCertificate209.phi 131072 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 131072) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 98304
  · exact FullPrefix209_002.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_003
