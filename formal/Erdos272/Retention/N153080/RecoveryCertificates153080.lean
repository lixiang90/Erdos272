module

public import Erdos272.Resources.N158375.LocalRecovery158375

@[expose] public section

namespace JSP233.RecoveryCertificates153080
open Recovery208 RecoveryParameters291012 LocalRecovery158375
noncomputable section
set_option maxHeartbeats 1000000

def CoarseA : ℝ := HLocal+433/100+144
def StrongA : ℝ := HLocal+433/100+17
def FineA : ℝ := HLocal+433/100
def FineW : ℝ := HLocal+13/2
def FineC : ℝ := 1733/2

theorem global_eighth :
    StageCertificate 151879 CoarseA BGlobal HLocal 2168 (1/8 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA,
    BGlobal, HLocal, LogLocal, CovarianceScalar213.Polynomial]

theorem coarse_local :
    StageCertificate 151879 CoarseA (BLocal 8) HLocal 2168 (3/25 : ℝ) (49/250) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

theorem strong_eighteenth :
    StageCertificate 151879 StrongA (BLocal 8) HLocal 872 (1/18 : ℝ) (1/10) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

theorem fine_final :
    StageCertificate 151879 FineA (BLocal 18) FineW FineC (1/25 : ℝ) (17/250) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA, FineW, FineC,
    BLocal, HLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]

#print axioms global_eighth
#print axioms coarse_local
#print axioms strong_eighteenth
#print axioms fine_final
end
end JSP233.RecoveryCertificates153080
