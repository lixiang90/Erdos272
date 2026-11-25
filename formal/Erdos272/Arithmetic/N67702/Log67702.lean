module

public import Erdos272.Arithmetic.N80470.Harmonic80470

@[expose] public section

namespace JSP233.Log67702
open StarCompletion HarmonicAbel29
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem endpoint_log : Real.log (80470 : ℝ)≤(113/10 : ℝ) := by
  have hr := Real.log_le_log (by norm_num : (0 : ℝ)<80470/98304)
    (by norm_num : (80470/98304 : ℝ)≤(639/640 : ℝ)^128)
  rw [Real.log_pow] at hr
  have hs := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<639/640)
  have h2 := LogThree126.log_two_window.2
  have h3 := LogThree126.log_three_window.2
  have he : Real.log (80470 : ℝ)=15*Real.log 2+Real.log 3+
      Real.log (80470/98304 : ℝ) := by
    rw [show (80470 : ℝ)=(2 : ℝ)^15*3*(80470/98304) by norm_num,
      Real.log_mul (by positivity) (by norm_num),
      Real.log_mul (by positivity) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  norm_num [LogThree126.TwoHi,LogThree126.ThreeHi] at h2 h3
  norm_num at hr hs
  linarith only [hr,hs,h2,h3]

theorem actual_log {N : ℕ} (hN : 1≤N) (hhi : N≤80469) :
    Real.log (N : ℝ)≤(113/10 : ℝ) := by
  have hn : (N : ℝ)≤80470 := by exact_mod_cast (show N≤80470 by omega)
  exact (Real.log_le_log (by exact_mod_cast (show 0<N by omega)) hn).trans endpoint_log

theorem actual_harmonic {N : ℕ} (hN : 10000≤N) (hhi : N≤80469) :
    Harmonic N≤(4759/400 : ℝ) :=
  Harmonic80470.actual_cap hN (by omega)

#print axioms endpoint_log
#print axioms actual_log
#print axioms actual_harmonic
end
end JSP233.Log67702
