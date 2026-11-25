module

public import Erdos272.Resources.N67702.LocalRecovery67702

@[expose] public section

namespace JSP233.RecoveryCertificates67702
open Recovery208 RecoveryParameters291012 LocalRecovery67702
noncomputable section
set_option maxHeartbeats 1000000

def CoarseA (k : ℕ) : ℝ := HLocal k+433/100+80489/1000-8/3
def FirstA (k : ℕ) : ℝ := HLocal k+433/100+1262/125-8/3
def MiddleA (k : ℕ) : ℝ := HLocal k+433/100+6193/1000-8/3
def StrongA (k : ℕ) : ℝ := HLocal k+112/100+2559/500
def GlobalW (k : ℕ) : ℝ := HLocal k-10493/5000
def CoarseW (k : ℕ) : ℝ := HLocal k-41622/10000
def FineA (k : ℕ) : ℝ := HLocal k+112/100
def FineW (k : ℕ) : ℝ := HLocal k+22928/10000
def FineC : ℝ := 1737/2

theorem global_seventh {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (CoarseA k) (BGlobal k+1) (GlobalW k) (872) (1/7 : ℝ) (1) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    CoarseA,FirstA,MiddleA,StrongA,FineA,GlobalW,CoarseW,FineW,FineC,
    BGlobal,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]

theorem first_stage {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (FirstA k) (BLocal k 7+1) (GlobalW k) (872) (1/14 : ℝ) (1/8) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    CoarseA,FirstA,MiddleA,StrongA,FineA,GlobalW,CoarseW,FineW,FineC,
    BGlobal,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]

theorem middle_stage {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (MiddleA k) (BLocal k 14+1) (GlobalW k) (872) (1/15 : ℝ) (14/125) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    CoarseA,FirstA,MiddleA,StrongA,FineA,GlobalW,CoarseW,FineW,FineC,
    BGlobal,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]

theorem strong_stage {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (StrongA k) (BLocal k 15+1/2) (CoarseW k) (874) (1/16 : ℝ) (11/100) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    CoarseA,FirstA,MiddleA,StrongA,FineA,GlobalW,CoarseW,FineW,FineC,
    BGlobal,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]

theorem fine_final {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (FineA k) (BLocal k 16+1/2) (FineW k) (FineC) (1/18 : ℝ) (3/32) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    CoarseA,FirstA,MiddleA,StrongA,FineA,GlobalW,CoarseW,FineW,FineC,
    BGlobal,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]

#print axioms global_seventh
#print axioms first_stage
#print axioms middle_stage
#print axioms strong_stage
#print axioms fine_final
end
end JSP233.RecoveryCertificates67702
