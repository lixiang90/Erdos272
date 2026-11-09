module

public import Erdos272.Retention.N200000.RecoveryCertificates200000

@[expose] public section
namespace JSP233.RecoveryProfiles200000
open StarCompletion HarmonicAbel29 Recovery208 RecoveryCaps213 RecoveryParameters291012
open RecoveryProfiles291012 RecoveryCertificates200000
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem coarse_bounds {N L : ℕ} {w : ℝ} (hN : 200000 ≤ N)
    (hc : Caps LogCap HCap N) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hp : RawProfile N L w CoarseA HCap 2168) :
    (L : ℝ) < (N : ℝ)/9 ∧ w < (1/5 : ℝ)*(N : ℝ) := by
  have hn : (200000 : ℝ) ≤ N := by exact_mod_cast hN
  have profile := global_profile hc hL hLN hp
  have hL4 : (L : ℝ) < (N : ℝ)/4 := by
    have hs := (actual_stage_bounds hn coarse_left_4 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 4) (by decide : 4 ≤ 33) hL4 hp
  have hL5 : (L : ℝ) < (N : ℝ)/5 := by
    have hs := (actual_stage_bounds hn coarse_left_5 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 5) (by decide : 5 ≤ 33) hL5 hp
  have hL6 : (L : ℝ) < (N : ℝ)/6 := by
    have hs := (actual_stage_bounds hn coarse_left_6 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 6) (by decide : 6 ≤ 33) hL6 hp
  have hL7 : (L : ℝ) < (N : ℝ)/7 := by
    have hs := (actual_stage_bounds hn coarse_left_7 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 7) (by decide : 7 ≤ 33) hL7 hp
  have hL8 : (L : ℝ) < (N : ℝ)/8 := by
    have hs := (actual_stage_bounds hn coarse_left_8 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 8) (by decide : 8 ≤ 33) hL8 hp
  have hL9 : (L : ℝ) < (N : ℝ)/9 := by
    have hs := (actual_stage_bounds hn coarse_left_9 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 9) (by decide : 9 ≤ 33) hL9 hp
  have hs := actual_stage_bounds hn coarse_width profile
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
#print axioms coarse_bounds

theorem strong_bounds {N L : ℕ} {w : ℝ} (hN : 200000 ≤ N)
    (hc : Caps LogCap HCap N) (hL : 1 ≤ L) (hknown : (L : ℝ) < (N : ℝ)/9)
    (hp : RawProfile N L w StrongA HCap 872) :
    (L : ℝ) < (N : ℝ)/16 ∧ w < (51/500 : ℝ)*(N : ℝ) := by
  have hn : (200000 : ℝ) ≤ N := by exact_mod_cast hN
  have profile := local_profile hc hL (by decide : 4 ≤ 9) (by decide : 9 ≤ 33) hknown hp
  have hL10 : (L : ℝ) < (N : ℝ)/10 := by
    have hs := (actual_stage_bounds hn strong_left_10 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 10) (by decide : 10 ≤ 33) hL10 hp
  have hL11 : (L : ℝ) < (N : ℝ)/11 := by
    have hs := (actual_stage_bounds hn strong_left_11 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 11) (by decide : 11 ≤ 33) hL11 hp
  have hL12 : (L : ℝ) < (N : ℝ)/12 := by
    have hs := (actual_stage_bounds hn strong_left_12 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 12) (by decide : 12 ≤ 33) hL12 hp
  have hL13 : (L : ℝ) < (N : ℝ)/13 := by
    have hs := (actual_stage_bounds hn strong_left_13 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 13) (by decide : 13 ≤ 33) hL13 hp
  have hL14 : (L : ℝ) < (N : ℝ)/14 := by
    have hs := (actual_stage_bounds hn strong_left_14 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 14) (by decide : 14 ≤ 33) hL14 hp
  have hL15 : (L : ℝ) < (N : ℝ)/15 := by
    have hs := (actual_stage_bounds hn strong_left_15 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 15) (by decide : 15 ≤ 33) hL15 hp
  have hL16 : (L : ℝ) < (N : ℝ)/16 := by
    have hs := (actual_stage_bounds hn strong_left_16 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 16) (by decide : 16 ≤ 33) hL16 hp
  have hs := actual_stage_bounds hn strong_width profile
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
#print axioms strong_bounds

theorem fine_bounds {N L : ℕ} {w : ℝ} (hN : 200000 ≤ N)
    (hc : Caps LogCap HCap N) (hL : 1 ≤ L) (hknown : (L : ℝ) < (N : ℝ)/16)
    (hp : RawProfile N L w FineA FineW200000 FineC200000) :
    (L : ℝ) < (N : ℝ)/27 ∧ w < (1/15 : ℝ)*(N : ℝ) := by
  have hn : (200000 : ℝ) ≤ N := by exact_mod_cast hN
  have profile := local_profile hc hL (by decide : 4 ≤ 16) (by decide : 16 ≤ 33) hknown hp
  have hL17 : (L : ℝ) < (N : ℝ)/17 := by
    have hs := (actual_stage_bounds hn fine_left_17 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 17) (by decide : 17 ≤ 33) hL17 hp
  have hL18 : (L : ℝ) < (N : ℝ)/18 := by
    have hs := (actual_stage_bounds hn fine_left_18 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 18) (by decide : 18 ≤ 33) hL18 hp
  have hL19 : (L : ℝ) < (N : ℝ)/19 := by
    have hs := (actual_stage_bounds hn fine_left_19 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 19) (by decide : 19 ≤ 33) hL19 hp
  have hL20 : (L : ℝ) < (N : ℝ)/20 := by
    have hs := (actual_stage_bounds hn fine_left_20 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 20) (by decide : 20 ≤ 33) hL20 hp
  have hL21 : (L : ℝ) < (N : ℝ)/21 := by
    have hs := (actual_stage_bounds hn fine_left_21 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 21) (by decide : 21 ≤ 33) hL21 hp
  have hL22 : (L : ℝ) < (N : ℝ)/22 := by
    have hs := (actual_stage_bounds hn fine_left_22 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 22) (by decide : 22 ≤ 33) hL22 hp
  have hL23 : (L : ℝ) < (N : ℝ)/23 := by
    have hs := (actual_stage_bounds hn fine_left_23 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 23) (by decide : 23 ≤ 33) hL23 hp
  have hL24 : (L : ℝ) < (N : ℝ)/24 := by
    have hs := (actual_stage_bounds hn fine_left_24 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 24) (by decide : 24 ≤ 33) hL24 hp
  have hL25 : (L : ℝ) < (N : ℝ)/25 := by
    have hs := (actual_stage_bounds hn fine_left_25 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 25) (by decide : 25 ≤ 33) hL25 hp
  have hL26 : (L : ℝ) < (N : ℝ)/26 := by
    have hs := (actual_stage_bounds hn fine_left_26 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 26) (by decide : 26 ≤ 33) hL26 hp
  have hL27 : (L : ℝ) < (N : ℝ)/27 := by
    have hs := (actual_stage_bounds hn fine_left_27 profile).1
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
  have profile := local_profile hc hL (by decide : 4 ≤ 27) (by decide : 27 ≤ 33) hL27 hp
  have hs := actual_stage_bounds hn fine_width profile
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs
#print axioms fine_bounds
end
end JSP233.RecoveryProfiles200000
