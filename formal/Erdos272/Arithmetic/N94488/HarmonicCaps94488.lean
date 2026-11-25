module

public import Erdos272.Resources.N158375.LocalRecovery158375

@[expose] public section

namespace JSP233.HarmonicCaps94488
open HarmonicAbel29 HarmonicCorrect118 HarmonicLog55
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem harmonic_log_5775 {N : ℕ} (hN : 10000 ≤ N) :
    Harmonic N ≤ Real.log N+231/400 := by
  have hm := corrected_harmonic_mono (M := 63) (by decide) (by omega : 63 ≤ N)
  norm_num only [Nat.cast_ofNat] at hm
  have hb : Harmonic 63-(6*(149337754816/215448838605 : ℝ)-1/63)-1/128 ≤ 57745/100000 := by
    rw [actual_harmonic63]
    norm_num
  have hn : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : (1 : ℝ)/(2*((N : ℝ)+1)) ≤ 1/20000 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith only [hn]
  linarith only [hm, hb, ht, actual_log63_lower]

theorem source_cap {N : ℕ} (hhi : N ≤ 179999) : Harmonic N ≤ (5107/400 : ℝ) := by
  have hc := LocalRecovery158375.actual_caps (N := 179999) (by norm_num) (by norm_num)
  exact (harmonic_mono hhi).trans (hc.harmonic_le.trans
    (by norm_num [LocalRecovery158375.HLocal]))

theorem log_anchor {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 15*Real.log 2+Real.log 3+(x-98304)/98304 := by
  have hr := Real.log_le_sub_one_of_pos (div_pos hx (by norm_num : (0 : ℝ) < 98304))
  have he : x = (2 : ℝ)^15*3*(x/98304) := by norm_num; ring
  have hlog : Real.log x = 15*Real.log 2+Real.log 3+Real.log (x/98304) := by
    conv_lhs => rw [he]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by norm_num),
      Real.log_pow]
    norm_num
  rw [hlog]
  linarith only [hr]

#print axioms harmonic_log_5775
#print axioms source_cap
#print axioms log_anchor
end
end JSP233.HarmonicCaps94488
