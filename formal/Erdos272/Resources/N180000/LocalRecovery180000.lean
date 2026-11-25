module

public import Erdos272.Retention.N291012.RecoveryProfiles291012
public import Erdos272.Arithmetic.LogThree126

@[expose] public section

namespace JSP233.LocalRecovery180000
open StarCompletion HarmonicAbel29 Recovery208 RecoveryCaps213 RecoveryParameters291012
open RecoveryProfiles291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def LogLocal : ℝ := 1219/100
def HLocal : ℝ := 5107/400
def BGlobal : ℝ := 102/25+2*HLocal+CovarianceScalar213.Polynomial LogLocal
def BLocal (j : ℕ) : ℝ := 102/25+2*(LogLocal-Lower j+61/100)+
  CovarianceScalar213.Polynomial (LogLocal-Lower j)

theorem actual_caps {N : ℕ} (hN : 100000 ≤ N) (hhi : N ≤ 189999) :
    Caps LogLocal HLocal N := by
  have hn : (N : ℝ) ≤ 3*(2 : ℝ)^16 := by exact_mod_cast (show N ≤ 3*2^16 by omega)
  have hl := Real.log_le_log (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega)) hn
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
  have h2 := LogThree126.log_two_window.2
  have h3 := LogThree126.log_three_window.2
  have hlog : Real.log (N : ℝ) ≤ LogLocal := by
    norm_num only [Nat.cast_ofNat] at hl
    norm_num [LogThree126.TwoHi, LogThree126.ThreeHi, LogLocal] at h2 h3 ⊢
    linarith only [hl, h2, h3]
  have hh := HarmonicCorrect118.actual_harmonic_log_5775 hN
  exact ⟨hlog, by dsimp only [HLocal, LogLocal] at *; linarith only [hlog, hh]⟩

theorem harmonic_log_61 {L : ℕ} (hL : 16 ≤ L) : Harmonic L ≤ Real.log L+61/100 := by
  have hm := HarmonicCorrect118.corrected_harmonic_mono (M := 16) (by decide) hL
  have hh : Harmonic 16 = (2436559/720720 : ℝ) := by
    norm_num [Harmonic, Finset.sum_Icc_succ_top]
  have hl : Real.log (16 : ℝ) = 4*Real.log 2 := by
    rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
    norm_num
  have htwo := LogThree126.log_two_window.1
  have hn : (16 : ℝ) ≤ L := by exact_mod_cast hL
  have ht : (1 : ℝ)/(2*((L : ℝ)+1)) ≤ 1/34 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith only [hn]
  norm_num only [Nat.cast_ofNat] at hm
  rw [hh, hl] at hm
  norm_num [LogThree126.TwoLo] at htwo
  linarith only [hm, ht, htwo]

theorem global_profile {N L : ℕ} {w A W C : ℝ}
    (hc : Caps LogLocal HLocal N) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hp : RawProfile N L w A W C) :
    WidthProfile L w ≤ A*N+BGlobal*L+W*w+C := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hl := (Real.log_le_log hLp (show (L : ℝ) ≤ N by exact_mod_cast hLN)).trans hc.log_le
  have hh := (ActualRecoveryChain208.harmonic_mono hLN).trans hc.harmonic_le
  have hpoly := RecoveryResource214.new_polynomial_mono (Real.log_nonneg (by exact_mod_cast hL)) hl
  have hcoeff : Coeff L ≤ BGlobal := by
    dsimp only [Coeff, BGlobal]
    linarith only [hh, hpoly]
  have hpaid := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (α := ℝ) L)
  dsimp only [RawProfile] at hp
  linarith only [hp, hpaid]

theorem local_profile {N L j : ℕ} {w A W C : ℝ}
    (hc : Caps LogLocal HLocal N) (hL : 1 ≤ L) (hj : 4 ≤ j) (hhi : j ≤ 33)
    (hleft : (L : ℝ) < (N : ℝ)/j) (hp : RawProfile N L w A W C) :
    WidthProfile L w ≤ A*N+BLocal j*L+W*w+C := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hlog := Real.log_le_log (mul_pos hLp hjp) ((le_div_iff₀ hjp).mp hleft.le)
  rw [Real.log_mul hLp.ne' hjp.ne'] at hlog
  have hsmall := lower_log hj hhi
  have hl : Real.log L ≤ LogLocal-Lower j := by linarith only [hlog, hsmall, hc.log_le]
  have hpoly := RecoveryResource214.new_polynomial_mono (Real.log_nonneg (by exact_mod_cast hL)) hl
  have hcoeff : Coeff L ≤ BLocal j := by
    by_cases h16 : 16 ≤ L
    · have hh := harmonic_log_61 h16
      dsimp only [Coeff, BLocal]
      linarith only [hh, hl, hpoly]
    · have hh := ActualRecoveryChain208.harmonic_mono (show L ≤ 16 by omega)
      have h16sum : Harmonic 16 ≤ 4 := by norm_num [Harmonic, Finset.sum_Icc_succ_top]
      have h16log : Real.log (16 : ℝ) ≤ 3 := by
        rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
        have ht := LogThree126.log_two_window.2
        norm_num [LogThree126.TwoHi] at ht ⊢
        linarith only [ht]
      have hl3 := (Real.log_le_log hLp (show (L : ℝ) ≤ 16 by exact_mod_cast (show L ≤ 16 by omega))).trans h16log
      have hp3 := RecoveryResource214.new_polynomial_mono (Real.log_nonneg (by exact_mod_cast hL)) hl3
      have hb : 18 ≤ BLocal j := by
        interval_cases j <;> norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial]
      dsimp only [Coeff, CovarianceScalar213.Polynomial]
      norm_num [CovarianceScalar213.Polynomial] at hp3
      linarith only [hh, h16sum, hp3, hb]
  have hpaid := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (α := ℝ) L)
  dsimp only [RawProfile] at hp
  linarith only [hp, hpaid]

#print axioms actual_caps
#print axioms harmonic_log_61
#print axioms global_profile
#print axioms local_profile
end
end JSP233.LocalRecovery180000
