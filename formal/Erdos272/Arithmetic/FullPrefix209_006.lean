import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_005
namespace JSP233.FullPrefix209_006
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem checked_part_196608 : DualFrontier209.checkFrom FactorFullCertificate209.phi 196608 8192 119523528010270651 11749660201 124503720048186956 12749206491 = true := by
  decide +kernel
#print axioms checked_part_196608
theorem checked_part_204800 : DualFrontier209.checkFrom FactorFullCertificate209.phi 204800 8192 124503720048186956 12749206491 129483830023963136 13789533471 = true := by
  decide +kernel
#print axioms checked_part_204800
theorem checked_part_212992 : DualFrontier209.checkFrom FactorFullCertificate209.phi 212992 8192 129483830023963136 13789533471 134463976167869802 14870665275 = true := by
  decide +kernel
#print axioms checked_part_212992
theorem checked_part_221184 : DualFrontier209.checkFrom FactorFullCertificate209.phi 221184 8192 134463976167869802 14870665275 139444106035683565 15992590767 = true := by
  decide +kernel
#print axioms checked_part_221184
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 196608 32768 119523528010270651 11749660201 139444106035683565 15992590767 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 196608 119523528010270651 11749660201 124503720048186956 12749206491 24576 139444106035683565 15992590767 checked_part_196608 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 204800 124503720048186956 12749206491 129483830023963136 13789533471 16384 139444106035683565 15992590767 checked_part_204800 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 212992 129483830023963136 13789533471 134463976167869802 14870665275 8192 139444106035683565 15992590767 checked_part_212992 checked_part_221184)))
theorem block_sound :
    (139444106035683565 = FrontierCheck209.massFloor FactorFullCertificate209.phi 229376 ∧
     15992590767 = FrontierCheck209.triangle FactorFullCertificate209.phi 229376) ∧
    ∀ t, 196608 < t → t ≤ 229376 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 196608 119523528010270651 11749660201 139444106035683565 15992590767 FullPrefix209_005.endpoint.1 FullPrefix209_005.endpoint.2 checked
theorem endpoint :
    139444106035683565 = FrontierCheck209.massFloor FactorFullCertificate209.phi 229376 ∧
    15992590767 = FrontierCheck209.triangle FactorFullCertificate209.phi 229376 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 229376) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 196608
  · exact FullPrefix209_005.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_006
