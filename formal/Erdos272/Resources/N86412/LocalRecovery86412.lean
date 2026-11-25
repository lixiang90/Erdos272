module

public import Erdos272.Resources.N118533.LocalRecovery118533
public import Erdos272.Arithmetic.N94488.HarmonicCaps94488

@[expose] public section

namespace JSP233.LocalRecovery86412
open StarCompletion HarmonicAbel29 Recovery208 RecoveryCaps213 RecoveryParameters291012
open RecoveryProfiles291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Low (k : ℕ) : ℕ := 86412
def High (k : ℕ) : ℕ := 88403
def LogLocal (k : ℕ) : ℝ := 1139/100
def HLocal (k : ℕ) : ℝ := LogLocal k+61/100
def BGlobal (k : ℕ) : ℝ := 102/25+2*HLocal k+CovarianceScalar213.Polynomial (LogLocal k)
def BLocal (k j : ℕ) : ℝ := 102/25+2*(LogLocal k-Lower j+61/100)+
  CovarianceScalar213.Polynomial (LogLocal k-Lower j)

theorem low_bound (k : ℕ) : 86412 ≤ Low k := by
  dsimp only [Low]
  omega

theorem high_bound (k : ℕ) : High k ≤ 88403 := by
  dsimp only [High]
  omega

theorem log_anchor {x : ℝ} (hx : 0<x) :
    Real.log x ≤ 18*Real.log 2-Real.log 3+(3*x-262144)/262144 := by
  let a : ℝ := (2 : ℝ)^18/3
  have ha : 0<a := by dsimp only [a]; positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [Real.log_div hx.ne' ha.ne'] at h
  have hl : Real.log a=18*Real.log 2-Real.log 3 := by
    dsimp only [a]
    rw [Real.log_div (by positivity) (by norm_num : (3 : ℝ)≠0), Real.log_pow]
    norm_num
  have he : x/a-1=(3*x-262144)/262144 := by
    norm_num [a]
    ring
  rw [hl, he] at h
  linarith only [h]

theorem actual_caps {N k : ℕ} (hk : k<1) (hN : 10000 ≤ N) (hhi : N ≤ High k) :
    Caps (LogLocal k) (HLocal k) N := by
  have hn : (N : ℝ) ≤ High k := by exact_mod_cast hhi
  have hl := log_anchor
    (show (0 : ℝ) < N by exact_mod_cast (show 0<N by omega))
  have h2 := LogThree126.log_two_window.2
  have h3 := LogThree126.log_three_window.1
  have hpay : 18*LogThree126.TwoHi-LogThree126.ThreeLo+
      (3*(High k : ℝ)-262144)/262144 ≤ LogLocal k := by
    interval_cases k <;> norm_num [High, LogLocal, LogThree126.TwoHi, LogThree126.ThreeLo]
  have hlog : Real.log (N : ℝ) ≤ LogLocal k := by
    linarith only [hn, hl, h2, h3, hpay]
  have hh := HarmonicCaps94488.harmonic_log_5775 hN
  exact ⟨hlog, by dsimp only [HLocal]; linarith only [hlog, hh]⟩

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
    · have hh := LocalRecovery118533.harmonic_log_local h1000
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
#print axioms log_anchor
#print axioms actual_caps
#print axioms global_profile
#print axioms local_profile
end
end JSP233.LocalRecovery86412
