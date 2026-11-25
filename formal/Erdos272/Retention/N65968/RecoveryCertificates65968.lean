module

public import Erdos272.Resources.N65968.LocalRecovery65968

@[expose] public section

namespace JSP233.RecoveryCertificates65968
open Recovery208 RecoveryParameters291012 LocalRecovery65968
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def CoarseA (k : ℕ) : ℝ := HLocal k+433/100+1611/20-8/3
def FirstA (k : ℕ) : ℝ := HLocal k+433/100+53/5-8/3
def MiddleA (k : ℕ) : ℝ := HLocal k+433/100+6-8/3
def GlobalW (k : ℕ) : ℝ := HLocal k-10493/5000
def WeakA (k : ℕ) : ℝ := HLocal k+112/100
def WeakW (k : ℕ) : ℝ := HLocal k-1-15811/5000+53/6
def WeakC : ℝ := 1735/2

theorem global_seventh {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (CoarseA k) (BGlobal k+1) (GlobalW k) (872) (1/7 : ℝ) (1) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    CoarseA,FirstA,MiddleA,GlobalW,WeakA,WeakW,WeakC,
    BGlobal,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]
#print axioms global_seventh

theorem first_thirteenth {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (FirstA k) (BLocal k 7+1) (GlobalW k) (872) (1/13 : ℝ) (1/8) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    CoarseA,FirstA,MiddleA,GlobalW,WeakA,WeakW,WeakC,
    BGlobal,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]
#print axioms first_thirteenth

theorem middle_short {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (MiddleA k) (BLocal k 13+1) (GlobalW k) (872) (1/15 : ℝ) (23/200) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    CoarseA,FirstA,MiddleA,GlobalW,WeakA,WeakW,WeakC,
    BGlobal,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]
#print axioms middle_short

theorem weak_box {k : ℕ} (hk : k<1) :
    StageCertificate (Low k) (WeakA k) (BLocal k 15+1/2) (WeakW k) (WeakC) (3/50 : ℝ) (51/500) := by
  interval_cases k <;> norm_num [Low,StageCertificate,LeftCentre,WidthCentre,ShiftEnergy,
    CoarseA,FirstA,MiddleA,GlobalW,WeakA,WeakW,WeakC,
    BGlobal,BLocal,HLocal,LogLocal,Lower,CovarianceScalar213.Polynomial]
#print axioms weak_box

end
end JSP233.RecoveryCertificates65968
