module

public import Erdos272.Resources.N80470.LocalRecovery80470
public import Erdos272.Resources.N118533.LocalRecovery118533
public import Erdos272.Arithmetic.N94488.HarmonicCaps94488
public import Erdos272.Arithmetic.N65968.Log65968

@[expose] public section

namespace JSP233.LocalRecovery65968
open StarCompletion HarmonicAbel29 Recovery208 RecoveryCaps213 RecoveryParameters291012
open RecoveryProfiles291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Low (_ : ℕ) : ℕ := 63616
def High (_ : ℕ) : ℕ := 67701
def LogLocal (_ : ℕ) : ℝ := 11123/1000
def HLocal (_ : ℕ) : ℝ := 23401/2000
def BGlobal (k : ℕ) : ℝ := 102/25+2*HLocal k+CovarianceScalar213.Polynomial (LogLocal k)
def BLocal (k j : ℕ) : ℝ := 102/25+2*(LogLocal k-Lower j+289/500)+
  CovarianceScalar213.Polynomial (LogLocal k-Lower j)

theorem low_bound (k : ℕ) : 63616 ≤ Low k := by
  exact Nat.le_refl _

theorem high_bound (k : ℕ) : High k ≤ 67701 := by
  exact Nat.le_refl _

theorem actual_caps {N k : ℕ} (hk : k<1) (hN : 10000≤N) (hhi : N≤High k) :
    Caps (LogLocal k) (HLocal k) N := by
  exact ⟨Log65968.actual_log (by omega) hhi,Log65968.actual_harmonic hN hhi⟩

theorem global_profile {N L k : ℕ} {w A W C : ℝ}
    (hc : Caps (LogLocal k) (HLocal k) N) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hp : RawProfile N L w A W C) :
    WidthProfile L w ≤ A*N+BGlobal k*L+W*w+C := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hl := (Real.log_le_log hLp (show (L : ℝ) ≤ N by exact_mod_cast hLN)).trans hc.log_le
  have hh := (ActualRecoveryChain208.harmonic_mono hLN).trans hc.harmonic_le
  have hpoly := RecoveryResource214.new_polynomial_mono (Real.log_nonneg (by exact_mod_cast hL)) hl
  have hcoeff : Coeff L ≤ BGlobal k := by
    dsimp only [Coeff, BGlobal]
    linarith only [hh, hpoly]
  have hpaid := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (α := ℝ) L)
  dsimp only [RawProfile] at hp
  linarith only [hp, hpaid]

theorem local_profile {N L j k : ℕ} {w A W C : ℝ}
    (hc : Caps (LogLocal k) (HLocal k) N) (hL : 1 ≤ L) (hj : 4 ≤ j) (hhi : j ≤ 33)
    (hB : (38 : ℝ) ≤ BLocal k j)
    (hleft : (L : ℝ) < (N : ℝ)/j) (hp : RawProfile N L w A W C) :
    WidthProfile L w ≤ A*N+BLocal k j*L+W*w+C := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hlog := Real.log_le_log (mul_pos hLp hjp) ((le_div_iff₀ hjp).mp hleft.le)
  rw [Real.log_mul hLp.ne' hjp.ne'] at hlog
  have hsmall := lower_log hj hhi
  have hl : Real.log L ≤ LogLocal k-Lower j := by linarith only [hlog, hsmall, hc.log_le]
  have hpoly := RecoveryResource214.new_polynomial_mono (Real.log_nonneg (by exact_mod_cast hL)) hl
  have hcoeff : Coeff L ≤ BLocal k j := by
    by_cases h1000 : 1000 ≤ L
    · have hh := LocalRecovery80470.harmonic_log_local h1000
      dsimp only [Coeff, BLocal]
      linarith only [hh, hl, hpoly]
    · have hh := ActualRecoveryChain208.harmonic_mono (show L ≤ 1024 by omega)
      have hH := HarmonicLog55.actual_harmonic_log_586 (N := 1024) (by decide)
      have hlog : Real.log (1024 : ℝ) = 10*Real.log 2 := by
        rw [show (1024 : ℝ) = 2^10 by norm_num, Real.log_pow]
        norm_num
      have htwo := LogThree126.log_two_window.2
      have hH8 : Harmonic 1024 ≤ 8 := by
        norm_num only [Nat.cast_ofNat] at hH
        rw [hlog] at hH
        norm_num [LogThree126.TwoHi] at htwo
        linarith only [hH, htwo]
      have hlog7 : Real.log (1024 : ℝ) ≤ 7 := by
        rw [hlog]
        norm_num [LogThree126.TwoHi] at htwo
        linarith only [htwo]
      have hl7 := (Real.log_le_log hLp (show (L : ℝ) ≤ 1024 by exact_mod_cast (show L ≤ 1024 by omega))).trans hlog7
      have hp7 := RecoveryResource214.new_polynomial_mono (Real.log_nonneg (by exact_mod_cast hL)) hl7
      dsimp only [Coeff, CovarianceScalar213.Polynomial]
      norm_num [CovarianceScalar213.Polynomial] at hp7
      linarith only [hh, hH8, hp7, hB]
  have hpaid := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (α := ℝ) L)
  dsimp only [RawProfile] at hp
  linarith only [hp, hpaid]

#print axioms low_bound
#print axioms high_bound
#print axioms actual_caps
#print axioms global_profile
#print axioms local_profile
end
end JSP233.LocalRecovery65968
