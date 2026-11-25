module

public import Erdos272.Resources.N158375.LocalRecovery158375

@[expose] public section

namespace JSP233.LocalRecovery150465
open StarCompletion HarmonicAbel29 Recovery208 RecoveryCaps213 RecoveryParameters291012
open RecoveryProfiles291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def LogLocal : ℝ := 597/50
def HLocal : ℝ := 5007/400
def BGlobal : ℝ := 102/25+2*HLocal+CovarianceScalar213.Polynomial LogLocal
def BLocal (j : ℕ) : ℝ := 102/25+2*(LogLocal-Lower j+289/500)+
  CovarianceScalar213.Polynomial (LogLocal-Lower j)

theorem endpoint_log : Real.log (153080 : ℝ) ≤ LogLocal := by
  have hr := Real.log_le_log (by norm_num : (0 : ℝ) < 19135/16384)
    (by norm_num : (19135/16384 : ℝ) ≤ (6311/6250 : ℝ)^16)
  rw [Real.log_pow] at hr
  have hs := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6311/6250)
  have h2 := LogThree126.log_two_window.2
  have hf : Real.log (153080 : ℝ) = 17*Real.log 2+Real.log (19135/16384 : ℝ) := by
    rw [show (153080 : ℝ) = (2 : ℝ)^17*(19135/16384) by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    norm_num
  rw [hf]
  norm_num [LogThree126.TwoHi, LogLocal] at h2 ⊢
  norm_num at hr hs
  linarith only [h2, hr, hs]

theorem actual_caps {N : ℕ} (hN : 100000 ≤ N) (hhi : N ≤ 153079) :
    Caps LogLocal HLocal N := by
  have hn : (N : ℝ) ≤ 153080 := by exact_mod_cast (show N ≤ 153080 by omega)
  have hl := Real.log_le_log (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega)) hn
  have hlog : Real.log (N : ℝ) ≤ LogLocal := hl.trans endpoint_log
  have hh := HarmonicCorrect118.actual_harmonic_log_5775 hN
  exact ⟨hlog, by dsimp only [HLocal, LogLocal] at *; linarith only [hlog, hh]⟩

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
    · have hh := LocalRecovery158375.harmonic_log_local h1000
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

#print axioms endpoint_log
#print axioms actual_caps
#print axioms global_profile
#print axioms local_profile
end
end JSP233.LocalRecovery150465
