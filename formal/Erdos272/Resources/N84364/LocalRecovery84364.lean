module

public import Erdos272.Resources.N86412.LocalRecovery86412

@[expose] public section

namespace JSP233.LocalRecovery84364
open StarCompletion HarmonicAbel29 Recovery208 RecoveryCaps213 RecoveryParameters291012
open RecoveryProfiles291012
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Low (_ : ℕ) : ℕ := 84364
def High (_ : ℕ) : ℕ := 86411
def LogLocal (_ : ℕ) : ℝ := 1139/100
def HLocal (k : ℕ) : ℝ := LogLocal k+61/100
def BGlobal (k : ℕ) : ℝ := 102/25+2*HLocal k+CovarianceScalar213.Polynomial (LogLocal k)
def BLocal (k j : ℕ) : ℝ := 102/25+2*(LogLocal k-Lower j+61/100)+
  CovarianceScalar213.Polynomial (LogLocal k-Lower j)

theorem low_bound (k : ℕ) : 84364 ≤ Low k := Nat.le_refl _
theorem high_bound (k : ℕ) : High k ≤ 86411 := Nat.le_refl _

theorem actual_caps {N k : ℕ} (hk : k < 1) (hN : 10000 ≤ N) (hhi : N ≤ High k) :
    Caps (LogLocal k) (HLocal k) N := by
  exact LocalRecovery86412.actual_caps hk hN
    (by dsimp only [High, LocalRecovery86412.High] at *; omega)

theorem global_profile {N L k : ℕ} {w A W C : ℝ}
    (hc : Caps (LogLocal k) (HLocal k) N) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hp : RawProfile N L w A W C) :
    WidthProfile L w ≤ A*N+BGlobal k*L+W*w+C := by
  exact LocalRecovery86412.global_profile (k := k) hc hL hLN hp

theorem local_profile {N L j k : ℕ} {w A W C : ℝ}
    (hc : Caps (LogLocal k) (HLocal k) N) (hL : 1 ≤ L) (hj : 4 ≤ j) (hhi : j ≤ 33)
    (hB : (38 : ℝ) ≤ BLocal k j)
    (hleft : (L : ℝ) < (N : ℝ)/j) (hp : RawProfile N L w A W C) :
    WidthProfile L w ≤ A*N+BLocal k j*L+W*w+C := by
  exact LocalRecovery86412.local_profile (k := k) hc hL hj hhi hB hleft hp

#print axioms low_bound
#print axioms high_bound
#print axioms actual_caps
#print axioms global_profile
#print axioms local_profile
end
end JSP233.LocalRecovery84364
