module

public import Erdos272.Retention.N291012.RecoveryProfiles291012
public import Erdos272.Arithmetic.LogThree126
public import Erdos272.Arithmetic.DirectMoment128

@[expose] public section

namespace JSP233.LocalRecovery118533
open StarCompletion HarmonicAbel29 Recovery208 RecoveryCaps213 RecoveryParameters291012
open RecoveryProfiles291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def LogLocal : ℝ := 11777/1000
def HLocal : ℝ := 24709/2000
def BGlobal : ℝ := 102/25+2*HLocal+CovarianceScalar213.Polynomial LogLocal
def BLocal (j : ℕ) : ℝ := 102/25+2*(LogLocal-Lower j+289/500)+
  CovarianceScalar213.Polynomial (LogLocal-Lower j)

theorem actual_caps {N : ℕ} (hN : 100000 ≤ N) (hhi : N ≤ 129999) :
    Caps LogLocal HLocal N := by
  have hn : (N : ℝ) ≤ 130000 := by exact_mod_cast (show N ≤ 130000 by omega)
  have hl := Real.log_le_log (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega)) hn
  have hf : Real.log (130000 : ℝ) = 17*Real.log 2+Real.log (8125/8192 : ℝ) := by
    rw [show (130000 : ℝ) = (2 : ℝ)^17*(8125/8192) by norm_num]
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    norm_num
  rw [hf] at hl
  have h2 := LogThree126.log_two_window.2
  have hr := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (8125/8192 : ℝ))
  have hlog : Real.log (N : ℝ) ≤ LogLocal := by
    norm_num [LogThree126.TwoHi, LogLocal] at h2 ⊢
    linarith only [hl, h2, hr]
  have hh := HarmonicCorrect118.actual_harmonic_log_5775 hN
  exact ⟨hlog, by dsimp only [HLocal, LogLocal] at *; linarith only [hlog, hh]⟩

theorem harmonic_log_local {L : ℕ} (hL : 1000 ≤ L) :
    Harmonic L ≤ Real.log L+289/500 := by
  have hm := HarmonicCorrect118.corrected_harmonic_mono (M := 63) (by decide) (by omega : 63 ≤ L)
  norm_num only [Nat.cast_ofNat] at hm
  have hb : Harmonic 63-(6*(149337754816/215448838605 : ℝ)-1/63)-1/128 ≤ 57745/100000 := by
    rw [HarmonicLog55.actual_harmonic63]
    norm_num
  have hn : (1000 : ℝ) ≤ L := by exact_mod_cast hL
  have ht : (1 : ℝ)/(2*((L : ℝ)+1)) ≤ 1/2002 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith only [hn]
  linarith only [hm, hb, ht, HarmonicLog55.actual_log63_lower]

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
    (hB : (38 : ℝ) ≤ BLocal j)
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
    by_cases h1000 : 1000 ≤ L
    · have hh := harmonic_log_local h1000
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

#print axioms actual_caps
#print axioms harmonic_log_local
#print axioms global_profile
#print axioms local_profile
end
end JSP233.LocalRecovery118533
