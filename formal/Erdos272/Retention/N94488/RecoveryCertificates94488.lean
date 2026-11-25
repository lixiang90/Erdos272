module

public import Erdos272.Resources.N94488.LocalRecovery94488

@[expose] public section

namespace JSP233.RecoveryCertificates94488
open Recovery208 RecoveryParameters291012 LocalRecovery94488
noncomputable section
set_option maxHeartbeats 1000000

def CoarseA (k : ℕ) : ℝ := HLocal k+433/100+86
def StrongA (k : ℕ) : ℝ := HLocal k+433/100+19/2
def FineA (k : ℕ) : ℝ := HLocal k+433/100
def FineW (k : ℕ) : ℝ := HLocal k+13/2
def FineC : ℝ := 1733/2

theorem global_eighth {k : ℕ} (hk : k<2) :
    StageCertificate (Low k) (CoarseA k) (BGlobal k) (HLocal k) 872 (1/8 : ℝ) 1 := by
  interval_cases k <;> norm_num [Low, StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA,
    BGlobal, HLocal, LogLocal, CovarianceScalar213.Polynomial]

theorem coarse_local {k : ℕ} (hk : k<2) :
    StageCertificate (Low k) (CoarseA k) (BLocal k 8) (HLocal k) 872 (3/25 : ℝ) (201/1000) := by
  interval_cases k <;> norm_num [Low, StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

theorem strong_stage {k : ℕ} (hk : k<2) :
    StageCertificate (Low k) (StrongA k) (BLocal k 8) (HLocal k) 872 (1/16 : ℝ) (11/100) := by
  interval_cases k <;> norm_num [Low, StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

theorem fine_final {k : ℕ} (hk : k<2) :
    StageCertificate (Low k) (FineA k) (BLocal k 16) (FineW k) FineC (1/19 : ℝ) (3/32) := by
  interval_cases k <;> norm_num [Low, StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA, FineW, FineC,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

#print axioms global_eighth
#print axioms coarse_local
#print axioms strong_stage
#print axioms fine_final
end
end JSP233.RecoveryCertificates94488
