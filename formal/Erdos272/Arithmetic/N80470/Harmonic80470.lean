module

public import Erdos272.Arithmetic.N94488.HarmonicCaps94488

@[expose] public section

namespace JSP233.Harmonic80470
open HarmonicAbel29
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem endpoint_log : Real.log (82427 : ℝ)≤(283/25 : ℝ) := by
  have hr := Real.log_le_log (by norm_num : (0 : ℝ)<82427/98304)
    (by norm_num : (82427/98304 : ℝ)≤(7989/8000 : ℝ)^128)
  rw [Real.log_pow] at hr
  have hs := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<7989/8000)
  have h2 := LogThree126.log_two_window.2
  have h3 := LogThree126.log_three_window.2
  have he : Real.log (82427 : ℝ)=15*Real.log 2+Real.log 3+
      Real.log (82427/98304 : ℝ) := by
    rw [show (82427 : ℝ)=(2 : ℝ)^15*3*(82427/98304) by norm_num,
      Real.log_mul (by positivity) (by norm_num),
      Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    norm_num
  rw [he]
  norm_num [LogThree126.TwoHi, LogThree126.ThreeHi] at h2 h3
  norm_num at hr hs
  linarith only [hr, hs, h2, h3]

theorem actual_cap {N : ℕ} (hN : 10000≤N) (hhi : N≤82427) :
    Harmonic N≤(4759/400 : ℝ) := by
  have hn : (N : ℝ)≤82427 := by exact_mod_cast hhi
  have hlog := (Real.log_le_log (by exact_mod_cast (show 0<N by omega)) hn).trans endpoint_log
  have hh := HarmonicCaps94488.harmonic_log_5775 hN
  linarith only [hlog, hh]

theorem actual_span_cap {N : ℕ} (hN : 10000≤N) (hhi : N≤82427) :
    Harmonic (N-1)≤(4759/400 : ℝ) :=
  (harmonic_mono (Nat.sub_le N 1)).trans (actual_cap hN hhi)

#print axioms endpoint_log
#print axioms actual_cap
#print axioms actual_span_cap
end
end JSP233.Harmonic80470
