module

public import Erdos272.Resources.N84364.LocalRecovery84364

@[expose] public section

namespace JSP233.RecoveryCertificates84364
open Recovery208 RecoveryParameters291012 LocalRecovery84364
noncomputable section
set_option maxHeartbeats 1000000

def CoarseA (k : ℕ) : ℝ := HLocal k+433/100+81
def QuarterA (k : ℕ) : ℝ := HLocal k+433/100+9
def StrongA (k : ℕ) : ℝ := HLocal k+433/100+25/4
def FineA (k : ℕ) : ℝ := HLocal k+433/100
def FineW (k : ℕ) : ℝ := HLocal k+13/2
def FineC : ℝ := 1733/2

theorem global_eighth {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (CoarseA k) (BGlobal k) (HLocal k) 872 (1/8 : ℝ) 1 := by
  interval_cases k <;> norm_num [Low, StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA,
    BGlobal, HLocal, LogLocal, CovarianceScalar213.Polynomial]

theorem coarse_local {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (CoarseA k) (BLocal k 8) (HLocal k) 872 (49/400 : ℝ) (21/100) := by
  interval_cases k <;> norm_num [Low, StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

theorem quarter_stage {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (QuarterA k) (BLocal k 8) (HLocal k) 872 (17/250 : ℝ) (14/125) := by
  interval_cases k <;> norm_num [Low, StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, QuarterA,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

theorem strong_stage {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (StrongA k) (BLocal k 14) (HLocal k) 872 (1/16 : ℝ) (11/100) := by
  interval_cases k <;> norm_num [Low, StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

theorem fine_final {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (FineA k) (BLocal k 16) (FineW k) FineC (27/500 : ℝ) (3/32) := by
  interval_cases k <;> norm_num [Low, StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA, FineW, FineC,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

#print axioms global_eighth
#print axioms coarse_local
#print axioms quarter_stage
#print axioms strong_stage
#print axioms fine_final
end
end JSP233.RecoveryCertificates84364
