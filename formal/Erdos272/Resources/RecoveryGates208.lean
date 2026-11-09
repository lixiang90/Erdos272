module

public import Erdos272.Resources.Recovery208

@[expose] public section

/-! Rational gates for the four round207 affine resources. These are
conditional algebraic implications; the actual family resources must still
be derived before any of these implications can be used. -/
namespace JSP233.RecoveryGates208
open Recovery208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def initialA : ℝ := (491419894309886851 / 3519605000000000 : ℝ)
def initialL : ℝ := (5917972401135192379912877897696201 / 49550477424100000000000000000000 : ℝ)
def initialW : ℝ := (49427898409886851 / 3519605000000000 : ℝ)
def initialC : ℝ := (993 / 1 : ℝ)

theorem initial_certificate :
    StageCertificate 659912 initialA initialL initialW initialC (5 / 97 : ℝ) (50 / 573 : ℝ) := by
  norm_num [StageCertificate, initialA, initialL, initialW, initialC,
    LeftCentre, WidthCentre, ShiftEnergy]

theorem initial_bounds {n L w : ℝ} (hn : 659912 ≤ n)
    (hprofile : WidthProfile L w ≤ initialA * n + initialL * L + initialW * w + initialC) :
    L < (5 / 97 : ℝ) * n ∧ w < (50 / 573 : ℝ) * n :=
  actual_stage_bounds hn initial_certificate hprofile

#print axioms initial_bounds

def after265A : ℝ := (65547689309886851 / 3519605000000000 : ℝ)
def after265L : ℝ := (272561426613030525536528955328569 / 3096904839006250000000000000000 : ℝ)
def after265W : ℝ := (118777416862947871613 / 221735115000000000 : ℝ)
def after265C : ℝ := (-78269 / 168 : ℝ)

theorem after265_certificate :
    StageCertificate 659912 after265A after265L after265W after265C (4 / 137 : ℝ) (20 / 401 : ℝ) := by
  norm_num [StageCertificate, after265A, after265L, after265W, after265C,
    LeftCentre, WidthCentre, ShiftEnergy]

theorem after265_bounds {n L w : ℝ} (hn : 659912 ≤ n)
    (hprofile : WidthProfile L w ≤ after265A * n + after265L * L + after265W * w + after265C) :
    L < (4 / 137 : ℝ) * n ∧ w < (20 / 401 : ℝ) * n :=
  actual_stage_bounds hn after265_certificate hprofile

#print axioms after265_bounds

def after24A : ℝ := (65547689309886851 / 3519605000000000 : ℝ)
def after24L : ℝ := (254961182729825013614019657511281 / 3096904839006250000000000000000 : ℝ)
def after24W : ℝ := (14783647927947871613 / 221735115000000000 : ℝ)
def after24C : ℝ := (187 / 168 : ℝ)

theorem after24_certificate :
    StageCertificate 659912 after24A after24L after24W after24C (5 / 248 : ℝ) (4 / 117 : ℝ) := by
  norm_num [StageCertificate, after24A, after24L, after24W, after24C,
    LeftCentre, WidthCentre, ShiftEnergy]

theorem after24_bounds {n L w : ℝ} (hn : 659912 ≤ n)
    (hprofile : WidthProfile L w ≤ after24A * n + after24L * L + after24W * w + after24C) :
    L < (5 / 248 : ℝ) * n ∧ w < (4 / 117 : ℝ) * n :=
  actual_stage_bounds hn after24_certificate hprofile

#print axioms after24_bounds

def after18A : ℝ := (65547689309886851 / 3519605000000000 : ℝ)
def after18L : ℝ := (624036566803418191714718250160321 / 7928076387856000000000000000000 : ℝ)
def after18W : ℝ := (11956525211697871613 / 221735115000000000 : ℝ)
def after18C : ℝ := (1909 / 168 : ℝ)

theorem after18_certificate :
    StageCertificate 659912 after18A after18L after18W after18C (5 / 251 : ℝ) (5 / 148 : ℝ) := by
  norm_num [StageCertificate, after18A, after18L, after18W, after18C,
    LeftCentre, WidthCentre, ShiftEnergy]

theorem after18_bounds {n L w : ℝ} (hn : 659912 ≤ n)
    (hprofile : WidthProfile L w ≤ after18A * n + after18L * L + after18W * w + after18C) :
    L < (5 / 251 : ℝ) * n ∧ w < (5 / 148 : ℝ) * n :=
  actual_stage_bounds hn after18_certificate hprofile

#print axioms after18_bounds

end
end JSP233.RecoveryGates208
