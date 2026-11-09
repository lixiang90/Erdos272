module

public import Erdos272.Arithmetic.RecoveryLocalization212
public import Erdos272.Resources.RecoveryOmitters212

@[expose] public section
namespace JSP233.RecoveryScalar212
open Recovery208 RecoveryGates208 RecoveryPrefix208 RecoveryLocalization212
open AlignedPlans212 RecoveryOmitters212
noncomputable section
set_option maxHeartbeats 0
def A (r : ℕ) : ℝ := if r=0 then initialA else HCap+229/50
def W (r : ℕ) : ℝ := if r=0 then initialW else HCap+PreparationA r+(PreparationP r : ℝ)-1
def C (r : ℕ) : ℝ := if r=0 then initialC else 26+PreparationB r-(PreparationP r : ℝ)

theorem initial_weak {n L w : ℝ} (hn : 656184≤n)
    (hp : WidthProfile L w ≤ A 0*n+(initialL)*L+W 0*w+C 0) :
    L<n/RecoveryLocalization212.Div 0 := by
  have hc : StageCertificate 656184 (A 0) (initialL) (W 0) (C 0) (1/RecoveryLocalization212.Div 0) (1) := by
    norm_num [StageCertificate,A,W,C,initialA,initialL,initialW,initialC,HCap,LogCap,
      LocalCoeff,LocalLog,Lower,RecoveryLocalization212.Div,FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms initial_weak

theorem initial_update {n L w : ℝ} (hn : 656184≤n)
    (hp : WidthProfile L w ≤ A 0*n+(LocalCoeff 0)*L+W 0*w+C 0) :
    L<n/RecoveryLocalization212.Div 1 := by
  have hc : StageCertificate 656184 (A 0) (LocalCoeff 0) (W 0) (C 0) (1/RecoveryLocalization212.Div 1) (1) := by
    norm_num [StageCertificate,A,W,C,initialA,initialL,initialW,initialC,HCap,LogCap,
      LocalCoeff,LocalLog,Lower,RecoveryLocalization212.Div,FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms initial_update

theorem initial_final {n L w : ℝ} (hn : 656184≤n)
    (hp : WidthProfile L w ≤ A 0*n+(LocalCoeff 1)*L+W 0*w+C 0) :
    L<n/RecoveryLocalization212.Div 1 ∧ w<n/(PreparationWidth 1) := by
  have hc : StageCertificate 656184 (A 0) (LocalCoeff 1) (W 0) (C 0) (1/RecoveryLocalization212.Div 1) (1/(PreparationWidth 1)) := by
    norm_num [StageCertificate,A,W,C,initialA,initialL,initialW,initialC,HCap,LogCap,
      LocalCoeff,LocalLog,Lower,RecoveryLocalization212.Div,FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh
#print axioms initial_final

theorem first_weak {n L w : ℝ} (hn : 656184≤n)
    (hp : WidthProfile L w ≤ A 1*n+(LocalCoeff 1)*L+W 1*w+C 1) :
    L<n/RecoveryLocalization212.Div 2 := by
  have hc : StageCertificate 656184 (A 1) (LocalCoeff 1) (W 1) (C 1) (1/RecoveryLocalization212.Div 2) (1) := by
    norm_num [StageCertificate,A,W,C,initialA,initialL,initialW,initialC,HCap,LogCap,
      LocalCoeff,LocalLog,Lower,RecoveryLocalization212.Div,FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms first_weak

theorem first_update {n L w : ℝ} (hn : 656184≤n)
    (hp : WidthProfile L w ≤ A 1*n+(LocalCoeff 2)*L+W 1*w+C 1) :
    L<n/RecoveryLocalization212.Div 3 := by
  have hc : StageCertificate 656184 (A 1) (LocalCoeff 2) (W 1) (C 1) (1/RecoveryLocalization212.Div 3) (1) := by
    norm_num [StageCertificate,A,W,C,initialA,initialL,initialW,initialC,HCap,LogCap,
      LocalCoeff,LocalLog,Lower,RecoveryLocalization212.Div,FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms first_update

theorem first_final {n L w : ℝ} (hn : 656184≤n)
    (hp : WidthProfile L w ≤ A 1*n+(LocalCoeff 3)*L+W 1*w+C 1) :
    L<n/RecoveryLocalization212.Div 4 ∧ w<n/(PreparationWidth 2) := by
  have hc : StageCertificate 656184 (A 1) (LocalCoeff 3) (W 1) (C 1) (1/RecoveryLocalization212.Div 4) (1/(PreparationWidth 2)) := by
    norm_num [StageCertificate,A,W,C,initialA,initialL,initialW,initialC,HCap,LogCap,
      LocalCoeff,LocalLog,Lower,RecoveryLocalization212.Div,FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh
#print axioms first_final

theorem second_weak {n L w : ℝ} (hn : 656184≤n)
    (hp : WidthProfile L w ≤ A 2*n+(LocalCoeff 4)*L+W 2*w+C 2) :
    L<n/RecoveryLocalization212.Div 5 := by
  have hc : StageCertificate 656184 (A 2) (LocalCoeff 4) (W 2) (C 2) (1/RecoveryLocalization212.Div 5) (1) := by
    norm_num [StageCertificate,A,W,C,initialA,initialL,initialW,initialC,HCap,LogCap,
      LocalCoeff,LocalLog,Lower,RecoveryLocalization212.Div,FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms second_weak

theorem second_update {n L w : ℝ} (hn : 656184≤n)
    (hp : WidthProfile L w ≤ A 2*n+(LocalCoeff 5)*L+W 2*w+C 2) :
    L<n/RecoveryLocalization212.Div 6 := by
  have hc : StageCertificate 656184 (A 2) (LocalCoeff 5) (W 2) (C 2) (1/RecoveryLocalization212.Div 6) (1) := by
    norm_num [StageCertificate,A,W,C,initialA,initialL,initialW,initialC,HCap,LogCap,
      LocalCoeff,LocalLog,Lower,RecoveryLocalization212.Div,FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms second_update

theorem second_final {n L w : ℝ} (hn : 656184≤n)
    (hp : WidthProfile L w ≤ A 2*n+(LocalCoeff 6)*L+W 2*w+C 2) :
    L<n/RecoveryLocalization212.Div 6 ∧ w<n/(PreparationWidth 3) := by
  have hc : StageCertificate 656184 (A 2) (LocalCoeff 6) (W 2) (C 2) (1/RecoveryLocalization212.Div 6) (1/(PreparationWidth 3)) := by
    norm_num [StageCertificate,A,W,C,initialA,initialL,initialW,initialC,HCap,LogCap,
      LocalCoeff,LocalLog,Lower,RecoveryLocalization212.Div,FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh
#print axioms second_final

theorem third_weak {n L w : ℝ} (hn : 656184≤n)
    (hp : WidthProfile L w ≤ A 3*n+(LocalCoeff 6)*L+W 3*w+C 3) :
    L<n/RecoveryLocalization212.Div 7 := by
  have hc : StageCertificate 656184 (A 3) (LocalCoeff 6) (W 3) (C 3) (1/RecoveryLocalization212.Div 7) (1) := by
    norm_num [StageCertificate,A,W,C,initialA,initialL,initialW,initialC,HCap,LogCap,
      LocalCoeff,LocalLog,Lower,RecoveryLocalization212.Div,FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh.1
#print axioms third_weak

theorem third_final {n L w : ℝ} (hn : 656184≤n)
    (hp : WidthProfile L w ≤ A 3*n+(LocalCoeff 7)*L+W 3*w+C 3) :
    L<n/RecoveryLocalization212.Div 7 ∧ w<n/(2951/100) := by
  have hc : StageCertificate 656184 (A 3) (LocalCoeff 7) (W 3) (C 3) (1/RecoveryLocalization212.Div 7) (1/(2951/100)) := by
    norm_num [StageCertificate,A,W,C,initialA,initialL,initialW,initialC,HCap,LogCap,
      LocalCoeff,LocalLog,Lower,RecoveryLocalization212.Div,FrontierSum208.Polynomial,PreparationA,PreparationB,
      PreparationWidth,PreparationP,LeftCentre,WidthCentre,ShiftEnergy]
  have hh := actual_stage_bounds hn hc hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh
#print axioms third_final
end
end JSP233.RecoveryScalar212
