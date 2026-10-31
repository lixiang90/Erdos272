import Erdos272.Arithmetic.RecoveryCaps213
namespace JSP233.RecoveryScalar213
open Recovery208 RecoveryCaps213 AlignedPlans212 RecoveryOmitters212
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem initial_weak {n L w : ℝ} (hn : 654848≤n)
    (hp : WidthProfile L w ≤ A HCap 0*n+(GlobalCoeff LogCap HCap)*L+W HCap 0*w+C 0) :
    L<n/RecoveryLocalization212.Div 0 := by
  have hc : StageCertificate 654848 (A HCap 0) (GlobalCoeff LogCap HCap) (W HCap 0) (C 0)
      (1/RecoveryLocalization212.Div 0) (1) := by
    norm_num [StageCertificate,A,W,C,HCap,LogCap,LocalCoeff,LocalLog,GlobalCoeff,
      RecoveryLocalization212.Lower,RecoveryLocalization212.Div,
      FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,RecoveryOmitters212.PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms initial_weak

theorem initial_update {n L w : ℝ} (hn : 654848≤n)
    (hp : WidthProfile L w ≤ A HCap 0*n+(LocalCoeff LogCap 0)*L+W HCap 0*w+C 0) :
    L<n/RecoveryLocalization212.Div 1 := by
  have hc : StageCertificate 654848 (A HCap 0) (LocalCoeff LogCap 0) (W HCap 0) (C 0)
      (1/RecoveryLocalization212.Div 1) (1) := by
    norm_num [StageCertificate,A,W,C,HCap,LogCap,LocalCoeff,LocalLog,GlobalCoeff,
      RecoveryLocalization212.Lower,RecoveryLocalization212.Div,
      FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,RecoveryOmitters212.PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms initial_update

theorem initial_final {n L w : ℝ} (hn : 654848≤n)
    (hp : WidthProfile L w ≤ A HCap 0*n+(LocalCoeff LogCap 1)*L+W HCap 0*w+C 0) :
    L<n/RecoveryLocalization212.Div 1 ∧ w<n/(PreparationWidth 1) := by
  have hc : StageCertificate 654848 (A HCap 0) (LocalCoeff LogCap 1) (W HCap 0) (C 0)
      (1/RecoveryLocalization212.Div 1) (1/(PreparationWidth 1)) := by
    norm_num [StageCertificate,A,W,C,HCap,LogCap,LocalCoeff,LocalLog,GlobalCoeff,
      RecoveryLocalization212.Lower,RecoveryLocalization212.Div,
      FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,RecoveryOmitters212.PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh
#print axioms initial_final

theorem first_weak {n L w : ℝ} (hn : 654848≤n)
    (hp : WidthProfile L w ≤ A HCap 1*n+(LocalCoeff LogCap 1)*L+W HCap 1*w+C 1) :
    L<n/RecoveryLocalization212.Div 2 := by
  have hc : StageCertificate 654848 (A HCap 1) (LocalCoeff LogCap 1) (W HCap 1) (C 1)
      (1/RecoveryLocalization212.Div 2) (1) := by
    norm_num [StageCertificate,A,W,C,HCap,LogCap,LocalCoeff,LocalLog,GlobalCoeff,
      RecoveryLocalization212.Lower,RecoveryLocalization212.Div,
      FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,RecoveryOmitters212.PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms first_weak

theorem first_update {n L w : ℝ} (hn : 654848≤n)
    (hp : WidthProfile L w ≤ A HCap 1*n+(LocalCoeff LogCap 2)*L+W HCap 1*w+C 1) :
    L<n/RecoveryLocalization212.Div 3 := by
  have hc : StageCertificate 654848 (A HCap 1) (LocalCoeff LogCap 2) (W HCap 1) (C 1)
      (1/RecoveryLocalization212.Div 3) (1) := by
    norm_num [StageCertificate,A,W,C,HCap,LogCap,LocalCoeff,LocalLog,GlobalCoeff,
      RecoveryLocalization212.Lower,RecoveryLocalization212.Div,
      FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,RecoveryOmitters212.PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms first_update

theorem first_final {n L w : ℝ} (hn : 654848≤n)
    (hp : WidthProfile L w ≤ A HCap 1*n+(LocalCoeff LogCap 3)*L+W HCap 1*w+C 1) :
    L<n/RecoveryLocalization212.Div 4 ∧ w<n/(PreparationWidth 2) := by
  have hc : StageCertificate 654848 (A HCap 1) (LocalCoeff LogCap 3) (W HCap 1) (C 1)
      (1/RecoveryLocalization212.Div 4) (1/(PreparationWidth 2)) := by
    norm_num [StageCertificate,A,W,C,HCap,LogCap,LocalCoeff,LocalLog,GlobalCoeff,
      RecoveryLocalization212.Lower,RecoveryLocalization212.Div,
      FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,RecoveryOmitters212.PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh
#print axioms first_final

theorem second_weak {n L w : ℝ} (hn : 654848≤n)
    (hp : WidthProfile L w ≤ A HCap 2*n+(LocalCoeff LogCap 4)*L+W HCap 2*w+C 2) :
    L<n/RecoveryLocalization212.Div 5 := by
  have hc : StageCertificate 654848 (A HCap 2) (LocalCoeff LogCap 4) (W HCap 2) (C 2)
      (1/RecoveryLocalization212.Div 5) (1) := by
    norm_num [StageCertificate,A,W,C,HCap,LogCap,LocalCoeff,LocalLog,GlobalCoeff,
      RecoveryLocalization212.Lower,RecoveryLocalization212.Div,
      FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,RecoveryOmitters212.PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms second_weak

theorem second_update {n L w : ℝ} (hn : 654848≤n)
    (hp : WidthProfile L w ≤ A HCap 2*n+(LocalCoeff LogCap 5)*L+W HCap 2*w+C 2) :
    L<n/RecoveryLocalization212.Div 6 := by
  have hc : StageCertificate 654848 (A HCap 2) (LocalCoeff LogCap 5) (W HCap 2) (C 2)
      (1/RecoveryLocalization212.Div 6) (1) := by
    norm_num [StageCertificate,A,W,C,HCap,LogCap,LocalCoeff,LocalLog,GlobalCoeff,
      RecoveryLocalization212.Lower,RecoveryLocalization212.Div,
      FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,RecoveryOmitters212.PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms second_update

theorem second_final {n L w : ℝ} (hn : 654848≤n)
    (hp : WidthProfile L w ≤ A HCap 2*n+(LocalCoeff LogCap 6)*L+W HCap 2*w+C 2) :
    L<n/RecoveryLocalization212.Div 6 ∧ w<n/(PreparationWidth 3) := by
  have hc : StageCertificate 654848 (A HCap 2) (LocalCoeff LogCap 6) (W HCap 2) (C 2)
      (1/RecoveryLocalization212.Div 6) (1/(PreparationWidth 3)) := by
    norm_num [StageCertificate,A,W,C,HCap,LogCap,LocalCoeff,LocalLog,GlobalCoeff,
      RecoveryLocalization212.Lower,RecoveryLocalization212.Div,
      FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,RecoveryOmitters212.PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh
#print axioms second_final

theorem third_weak {n L w : ℝ} (hn : 654848≤n)
    (hp : WidthProfile L w ≤ A HCap 3*n+(LocalCoeff LogCap 6)*L+W HCap 3*w+C 3) :
    L<n/RecoveryLocalization212.Div 7 := by
  have hc : StageCertificate 654848 (A HCap 3) (LocalCoeff LogCap 6) (W HCap 3) (C 3)
      (1/RecoveryLocalization212.Div 7) (1) := by
    norm_num [StageCertificate,A,W,C,HCap,LogCap,LocalCoeff,LocalLog,GlobalCoeff,
      RecoveryLocalization212.Lower,RecoveryLocalization212.Div,
      FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,RecoveryOmitters212.PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms third_weak

theorem third_final {n L w : ℝ} (hn : 654848≤n)
    (hp : WidthProfile L w ≤ A HCap 3*n+(LocalCoeff LogCap 7)*L+W HCap 3*w+C 3) :
    L<n/RecoveryLocalization212.Div 7 ∧ w<n/(2951/100) := by
  have hc : StageCertificate 654848 (A HCap 3) (LocalCoeff LogCap 7) (W HCap 3) (C 3)
      (1/RecoveryLocalization212.Div 7) (1/(2951/100)) := by
    norm_num [StageCertificate,A,W,C,HCap,LogCap,LocalCoeff,LocalLog,GlobalCoeff,
      RecoveryLocalization212.Lower,RecoveryLocalization212.Div,
      FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,RecoveryOmitters212.PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh
#print axioms third_final
end
end JSP233.RecoveryScalar213
