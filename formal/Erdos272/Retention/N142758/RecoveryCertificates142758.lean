module

public import Erdos272.Resources.N158375.LocalRecovery158375

@[expose] public section

namespace JSP233.RecoveryCertificates142758
open Recovery208 RecoveryParameters291012 LocalRecovery158375
noncomputable section
set_option maxHeartbeats 1000000

def CoarseA : ℝ := HLocal+433/100+103
def StrongA : ℝ := HLocal+433/100+17
def FineA : ℝ := HLocal+433/100
def FineW : ℝ := HLocal+13/2
def FineC : ℝ := 1733/2

theorem global_eighth :
    StageCertificate 130000 CoarseA BGlobal HLocal 872 (1/8 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA,
    BGlobal, HLocal, LogLocal, CovarianceScalar213.Polynomial]

theorem coarse_local :
    StageCertificate 130000 CoarseA (BLocal 8) HLocal 872 (3/25 : ℝ) (49/250) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

theorem strong_stage :
    StageCertificate 130000 StrongA (BLocal 8) HLocal 872 (2/33 : ℝ) (11/100) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

theorem fine_final :
    StageCertificate 130000 FineA (BLocal 16) FineW FineC (1/20 : ℝ) (2/25) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA, FineW, FineC,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

#print axioms global_eighth
#print axioms coarse_local
#print axioms strong_stage
#print axioms fine_final
end
end JSP233.RecoveryCertificates142758
