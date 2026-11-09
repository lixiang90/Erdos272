module

public import Erdos272.Retention.N291012.RecoveryCertificates291012

@[expose] public section

namespace JSP233.RecoveryProfiles291012
open StarCompletion HarmonicAbel29 Recovery208 RecoveryCaps213 RecoveryParameters291012
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Coeff (L : ℕ) : ℝ :=
  102/25+2*Harmonic L+CovarianceScalar213.Polynomial (Real.log L)

def RawProfile (N L : ℕ) (w A W C : ℝ) : Prop :=
  WidthProfile L w ≤ A*N+Coeff L*L+W*w+C

theorem lower_log {j : ℕ} (hj : 4 ≤ j) (hhi : j ≤ 33) :
    Lower j ≤ Real.log (j : ℝ) := by
  interval_cases j
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_4).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable131.state_5).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable131.state_6).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable131.state_7).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_8).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_9).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable131.state_10).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_11).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_12).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_13).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable131.state_14).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable131.state_15).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_16).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_17).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_18).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_19).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_20).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable131.state_21).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_22).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_23).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_24).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_25).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_26).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_27).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_28).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_29).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable131.state_30).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_31).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_32).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh
  · have hh := (PrefixLog131.log_bounds (by decide) PrefixTable132.state_33).1
    norm_num [Lower, PrefixTable131.grid] at hh ⊢
    exact hh

theorem local_numeric {j : ℕ} (hj : 4 ≤ j) (hhi : j ≤ 33) :
    102/25+2*(LogCap-Lower j+1)+
      CovarianceScalar213.Polynomial (LogCap-Lower j) ≤ LocalB j := by
  interval_cases j <;> norm_num [LogCap, Lower, LocalB, CovarianceScalar213.Polynomial]

theorem global_profile {N L : ℕ} {w A W C : ℝ}
    (hc : Caps LogCap HCap N) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hp : RawProfile N L w A W C) :
    WidthProfile L w ≤ A*N+GlobalB*L+W*w+C := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hl := (Real.log_le_log hLp (show (L : ℝ) ≤ N by exact_mod_cast hLN)).trans hc.log_le
  have hh := (ActualRecoveryChain208.harmonic_mono hLN).trans hc.harmonic_le
  have hpoly := RecoveryResource214.new_polynomial_mono (Real.log_nonneg (by exact_mod_cast hL)) hl
  have hnumeric : 102/25+2*HCap+CovarianceScalar213.Polynomial LogCap ≤ GlobalB := by
    norm_num [HCap, LogCap, GlobalB, CovarianceScalar213.Polynomial]
  have hcoeff : Coeff L ≤ GlobalB := by
    dsimp only [Coeff]
    linarith only [hh, hpoly, hnumeric]
  have hpaid := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (α := ℝ) L)
  dsimp only [RawProfile] at hp
  linarith only [hp, hpaid]

theorem local_profile {N L j : ℕ} {w A W C : ℝ}
    (hc : Caps LogCap HCap N) (hL : 1 ≤ L) (hj : 4 ≤ j) (hhi : j ≤ 33)
    (hleft : (L : ℝ) < (N : ℝ)/j) (hp : RawProfile N L w A W C) :
    WidthProfile L w ≤ A*N+LocalB j*L+W*w+C := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hjp : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hmult := (le_div_iff₀ hjp).mp hleft.le
  have hlog := Real.log_le_log (mul_pos hLp hjp) hmult
  rw [Real.log_mul hLp.ne' hjp.ne'] at hlog
  have hsmall := lower_log hj hhi
  have hl : Real.log L ≤ LogCap-Lower j := by linarith only [hlog, hsmall, hc.log_le]
  have hh := HarmonicAbel29.harmonic_le_one_add_log L
  have hpoly := RecoveryResource214.new_polynomial_mono (Real.log_nonneg (by exact_mod_cast hL)) hl
  have hnumeric := local_numeric hj hhi
  have hcoeff : Coeff L ≤ LocalB j := by
    dsimp only [Coeff]
    linarith only [hh, hl, hpoly, hnumeric]
  have hpaid := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (α := ℝ) L)
  dsimp only [RawProfile] at hp
  linarith only [hp, hpaid]

theorem coarse_bounds {N L : ℕ} {w : ℝ}
    (hN : 291012 ≤ N) (hc : Caps LogCap HCap N) (hL : 1 ≤ L)
    (hLN : L ≤ N)
    (hp : RawProfile N L w CoarseA HCap 2168) :
    (L : ℝ) < (N : ℝ)/11 ∧ w < (N : ℝ)/7 := by
  have hn : (291012 : ℝ) ≤ N := by exact_mod_cast hN
  have profile := global_profile hc hL hLN hp
  have hL4 : (L : ℝ) < (N : ℝ)/4 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.coarse_left_4 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 4) (by decide : 4 ≤ 33) hL4 hp
  have hL5 : (L : ℝ) < (N : ℝ)/5 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.coarse_left_5 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 5) (by decide : 5 ≤ 33) hL5 hp
  have hL6 : (L : ℝ) < (N : ℝ)/6 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.coarse_left_6 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 6) (by decide : 6 ≤ 33) hL6 hp
  have hL7 : (L : ℝ) < (N : ℝ)/7 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.coarse_left_7 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 7) (by decide : 7 ≤ 33) hL7 hp
  have hL8 : (L : ℝ) < (N : ℝ)/8 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.coarse_left_8 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 8) (by decide : 8 ≤ 33) hL8 hp
  have hL9 : (L : ℝ) < (N : ℝ)/9 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.coarse_left_9 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 9) (by decide : 9 ≤ 33) hL9 hp
  have hL10 : (L : ℝ) < (N : ℝ)/10 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.coarse_left_10 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 10) (by decide : 10 ≤ 33) hL10 hp
  have hL11 : (L : ℝ) < (N : ℝ)/11 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.coarse_left_11 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 11) (by decide : 11 ≤ 33) hL11 hp
  have hs := actual_stage_bounds hn RecoveryCertificates291012.coarse_width profile
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs

theorem strong_bounds {N L : ℕ} {w : ℝ}
    (hN : 291012 ≤ N) (hc : Caps LogCap HCap N) (hL : 1 ≤ L)
    (hknown : (L : ℝ) < (N : ℝ)/11)
    (hp : RawProfile N L w StrongA HCap 872) :
    (L : ℝ) < (N : ℝ)/20 ∧ w < (4/47 : ℝ)*(N : ℝ) := by
  have hn : (291012 : ℝ) ≤ N := by exact_mod_cast hN
  have profile := local_profile hc hL (by decide : 4 ≤ 11) (by decide : 11 ≤ 33) hknown hp
  have hL12 : (L : ℝ) < (N : ℝ)/12 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.strong_left_12 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 12) (by decide : 12 ≤ 33) hL12 hp
  have hL13 : (L : ℝ) < (N : ℝ)/13 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.strong_left_13 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 13) (by decide : 13 ≤ 33) hL13 hp
  have hL14 : (L : ℝ) < (N : ℝ)/14 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.strong_left_14 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 14) (by decide : 14 ≤ 33) hL14 hp
  have hL15 : (L : ℝ) < (N : ℝ)/15 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.strong_left_15 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 15) (by decide : 15 ≤ 33) hL15 hp
  have hL16 : (L : ℝ) < (N : ℝ)/16 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.strong_left_16 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 16) (by decide : 16 ≤ 33) hL16 hp
  have hL17 : (L : ℝ) < (N : ℝ)/17 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.strong_left_17 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 17) (by decide : 17 ≤ 33) hL17 hp
  have hL18 : (L : ℝ) < (N : ℝ)/18 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.strong_left_18 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 18) (by decide : 18 ≤ 33) hL18 hp
  have hL19 : (L : ℝ) < (N : ℝ)/19 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.strong_left_19 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 19) (by decide : 19 ≤ 33) hL19 hp
  have hL20 : (L : ℝ) < (N : ℝ)/20 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.strong_left_20 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 20) (by decide : 20 ≤ 33) hL20 hp
  have hs := actual_stage_bounds hn RecoveryCertificates291012.strong_width profile
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs

theorem fine1_bounds {N L : ℕ} {w : ℝ}
    (hN : 291012 ≤ N) (hc : Caps LogCap HCap N) (hL : 1 ≤ L)
    (hknown : (L : ℝ) < (N : ℝ)/20)
    (hp : RawProfile N L w FineA FineW1 FineC1) :
    (L : ℝ) < (N : ℝ)/33 ∧ w < (2/39 : ℝ)*(N : ℝ) := by
  have hn : (291012 : ℝ) ≤ N := by exact_mod_cast hN
  have profile := local_profile hc hL (by decide : 4 ≤ 20) (by decide : 20 ≤ 33) hknown hp
  have hL21 : (L : ℝ) < (N : ℝ)/21 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_21 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 21) (by decide : 21 ≤ 33) hL21 hp
  have hL22 : (L : ℝ) < (N : ℝ)/22 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_22 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 22) (by decide : 22 ≤ 33) hL22 hp
  have hL23 : (L : ℝ) < (N : ℝ)/23 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_23 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 23) (by decide : 23 ≤ 33) hL23 hp
  have hL24 : (L : ℝ) < (N : ℝ)/24 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_24 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 24) (by decide : 24 ≤ 33) hL24 hp
  have hL25 : (L : ℝ) < (N : ℝ)/25 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_25 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 25) (by decide : 25 ≤ 33) hL25 hp
  have hL26 : (L : ℝ) < (N : ℝ)/26 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_26 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 26) (by decide : 26 ≤ 33) hL26 hp
  have hL27 : (L : ℝ) < (N : ℝ)/27 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_27 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 27) (by decide : 27 ≤ 33) hL27 hp
  have hL28 : (L : ℝ) < (N : ℝ)/28 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_28 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 28) (by decide : 28 ≤ 33) hL28 hp
  have hL29 : (L : ℝ) < (N : ℝ)/29 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_29 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 29) (by decide : 29 ≤ 33) hL29 hp
  have hL30 : (L : ℝ) < (N : ℝ)/30 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_30 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 30) (by decide : 30 ≤ 33) hL30 hp
  have hL31 : (L : ℝ) < (N : ℝ)/31 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_31 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 31) (by decide : 31 ≤ 33) hL31 hp
  have hL32 : (L : ℝ) < (N : ℝ)/32 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_32 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 32) (by decide : 32 ≤ 33) hL32 hp
  have hL33 : (L : ℝ) < (N : ℝ)/33 := by
    have hs := (actual_stage_bounds hn RecoveryCertificates291012.fine1_left_33 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 33) (by decide : 33 ≤ 33) hL33 hp
  have hs := actual_stage_bounds hn RecoveryCertificates291012.fine1_width profile
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs

theorem fine2_bounds {N L : ℕ} {w : ℝ}
    (hN : 291012 ≤ N) (hc : Caps LogCap HCap N) (hL : 1 ≤ L)
    (hknown : (L : ℝ) < (N : ℝ)/33)
    (hp : RawProfile N L w FineA FineW2 FineC2) :
    (L : ℝ) < (N : ℝ)/33 ∧ w < (4/79 : ℝ)*(N : ℝ) := by
  have hn : (291012 : ℝ) ≤ N := by exact_mod_cast hN
  have profile := local_profile hc hL (by decide : 4 ≤ 33) (by decide : 33 ≤ 33) hknown hp
  have hs := actual_stage_bounds hn RecoveryCertificates291012.fine2_width profile
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs

#print axioms lower_log
#print axioms local_numeric
#print axioms global_profile
#print axioms local_profile
#print axioms coarse_bounds
#print axioms strong_bounds
#print axioms fine1_bounds
#print axioms fine2_bounds
end
end JSP233.RecoveryProfiles291012
