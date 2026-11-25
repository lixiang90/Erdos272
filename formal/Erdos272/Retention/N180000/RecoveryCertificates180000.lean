module

public import Erdos272.Resources.N180000.LocalRecovery180000
public import Erdos272.Retention.N291012.RecoveryProfiles291012

@[expose] public section

namespace JSP233.RecoveryCertificates180000
open Recovery208 RecoveryCaps213 RecoveryParameters291012
open LocalRecovery180000
noncomputable section
set_option maxHeartbeats 1000000
def CoarseA180000 : ℝ := HLocal+433/100+144
def StrongA180000 : ℝ := HLocal+433/100+3601/100
def FineA180000 : ℝ := HLocal+433/100

def FineW180000 : ℝ := HLocal+1337/60
def FineC180000 : ℝ := 872-297/20
def SecondW180000 : ℝ := HLocal+947/60
def SecondC180000 : ℝ := 872-187/20

theorem coarse_left_4 : StageCertificate 180000 CoarseA180000 BGlobal HLocal 2168 (1/4 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA180000, BGlobal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms coarse_left_4

theorem coarse_left_5 : StageCertificate 180000 CoarseA180000 (BLocal 4) HLocal 2168 (1/5 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms coarse_left_5

theorem coarse_left_6 : StageCertificate 180000 CoarseA180000 (BLocal 5) HLocal 2168 (1/6 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms coarse_left_6

theorem coarse_left_7 : StageCertificate 180000 CoarseA180000 (BLocal 6) HLocal 2168 (1/7 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms coarse_left_7

theorem coarse_left_8 : StageCertificate 180000 CoarseA180000 (BLocal 7) HLocal 2168 (1/8 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms coarse_left_8

theorem coarse_left_9 : StageCertificate 180000 CoarseA180000 (BLocal 8) HLocal 2168 (1/9 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms coarse_left_9

theorem coarse_width : StageCertificate 180000 CoarseA180000 (BLocal 9) HLocal 2168 (1/9 : ℝ) (1/5 : ℝ) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms coarse_width

theorem strong_left_10 : StageCertificate 180000 StrongA180000 (BLocal 9) HLocal 872 (1/10 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms strong_left_10

theorem strong_left_11 : StageCertificate 180000 StrongA180000 (BLocal 10) HLocal 872 (1/11 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms strong_left_11

theorem strong_left_12 : StageCertificate 180000 StrongA180000 (BLocal 11) HLocal 872 (1/12 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms strong_left_12

theorem strong_left_13 : StageCertificate 180000 StrongA180000 (BLocal 12) HLocal 872 (1/13 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms strong_left_13

theorem strong_left_14 : StageCertificate 180000 StrongA180000 (BLocal 13) HLocal 872 (1/14 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms strong_left_14

theorem strong_left_15 : StageCertificate 180000 StrongA180000 (BLocal 14) HLocal 872 (1/15 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms strong_left_15

theorem strong_left_16 : StageCertificate 180000 StrongA180000 (BLocal 15) HLocal 872 (1/16 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms strong_left_16

theorem strong_width : StageCertificate 180000 StrongA180000 (BLocal 16) HLocal 872 (1/16 : ℝ) (53/500 : ℝ) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms strong_width

theorem fine_left_17 : StageCertificate 180000 FineA180000 (BLocal 16) FineW180000 FineC180000 (1/17 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA180000, FineW180000, FineC180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms fine_left_17

theorem fine_left_18 : StageCertificate 180000 FineA180000 (BLocal 17) FineW180000 FineC180000 (1/18 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA180000, FineW180000, FineC180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms fine_left_18

theorem fine_left_19 : StageCertificate 180000 FineA180000 (BLocal 18) FineW180000 FineC180000 (1/19 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA180000, FineW180000, FineC180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms fine_left_19

theorem fine_left_20 : StageCertificate 180000 FineA180000 (BLocal 19) FineW180000 FineC180000 (1/20 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA180000, FineW180000, FineC180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms fine_left_20

theorem fine_left_21 : StageCertificate 180000 FineA180000 (BLocal 20) FineW180000 FineC180000 (1/21 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA180000, FineW180000, FineC180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms fine_left_21

theorem fine_left_22 : StageCertificate 180000 FineA180000 (BLocal 21) FineW180000 FineC180000 (1/22 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA180000, FineW180000, FineC180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms fine_left_22

theorem fine_left_23 : StageCertificate 180000 FineA180000 (BLocal 22) FineW180000 FineC180000 (1/23 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA180000, FineW180000, FineC180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms fine_left_23

theorem fine_left_24 : StageCertificate 180000 FineA180000 (BLocal 23) FineW180000 FineC180000 (1/24 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA180000, FineW180000, FineC180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms fine_left_24

theorem fine_left_25 : StageCertificate 180000 FineA180000 (BLocal 24) FineW180000 FineC180000 (1/25 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA180000, FineW180000, FineC180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms fine_left_25

theorem fine_left_26 : StageCertificate 180000 FineA180000 (BLocal 25) FineW180000 FineC180000 (1/26 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA180000, FineW180000, FineC180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms fine_left_26

theorem fine_width : StageCertificate 180000 FineA180000 (BLocal 26) FineW180000 FineC180000 (1/26 : ℝ) (1/15 : ℝ) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA180000, FineW180000, FineC180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms fine_width

theorem second_width : StageCertificate 180000 FineA180000 (BLocal 26) SecondW180000 SecondC180000 (1/26 : ℝ) (6273/100000 : ℝ) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA180000, SecondW180000, SecondC180000, BLocal, HLocal, LogLocal, CovarianceScalar213.Polynomial, Lower]
#print axioms second_width
end
end JSP233.RecoveryCertificates180000
