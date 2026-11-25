module

public import Erdos272.Resources.N80470.LocalRecovery80470

@[expose] public section

namespace JSP233.RecoveryCertificates80470
open Recovery208 RecoveryParameters291012 LocalRecovery80470
noncomputable section
set_option maxHeartbeats 1000000

def CoarseA (k : ℕ) : ℝ := HLocal k+433/100+1609/20
def FirstA (k : ℕ) : ℝ := HLocal k+433/100+9063/1000
def MiddleA (k : ℕ) : ℝ := HLocal k+433/100+1239/200
def StrongA (k : ℕ) : ℝ := HLocal k+433/100+109/20
def FineA (k : ℕ) : ℝ := HLocal k+383/100
def FineW (k : ℕ) : ℝ := HLocal k+13/2
def FineC : ℝ := 1733/2

theorem global_seventh {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (CoarseA k) (BGlobal k) (HLocal k) 872 (1/7 : ℝ) 1 := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    CoarseA,BGlobal,HLocal,LogLocal,CovarianceScalar213.Polynomial]

theorem first_stage {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (FirstA k) (BLocal k 7) (HLocal k) 872 (1/14 : ℝ) (23/200) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    FirstA,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]

theorem middle_stage {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (MiddleA k) (BLocal k 14) (HLocal k) 872 (1/15 : ℝ) (11/100) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    MiddleA,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]

theorem strong_stage {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (StrongA k) (BLocal k 15) (HLocal k) 872 (1/16 : ℝ) (11/100) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    StrongA,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]

theorem fine_final {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (FineA k) (BLocal k 16) (FineW k) FineC (1/18 : ℝ) (3/32) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    FineA,FineW,FineC,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]

#print axioms global_seventh
#print axioms first_stage
#print axioms middle_stage
#print axioms strong_stage
#print axioms fine_final
end
end JSP233.RecoveryCertificates80470
