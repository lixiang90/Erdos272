module

public import Erdos272.Arithmetic.N94488.HarmonicCaps94488
public import Erdos272.Arithmetic.LogThree126

@[expose] public section

namespace JSP233.Log65968
open StarCompletion HarmonicAbel29
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem endpoint_log : Real.log (67702 : ℝ)≤(11123/1000 : ℝ) := by
  have hr:=Real.log_le_log (by norm_num : (0 : ℝ)<67702/65536)
    (by norm_num : (67702/65536 : ℝ)≤(308/307 : ℝ)^10)
  rw [Real.log_pow] at hr
  have hs:=Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<308/307)
  have h2:=LogThree126.log_two_window.2
  have he : Real.log (67702 : ℝ)=16*Real.log 2+Real.log (67702/65536 : ℝ) := by
    rw [show (67702 : ℝ)=(2 : ℝ)^16*(67702/65536) by norm_num,
      Real.log_mul (by positivity) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  norm_num [LogThree126.TwoHi] at h2
  norm_num at hr hs
  linarith only [hr,hs,h2]

theorem actual_log {N : ℕ} (hN : 1≤N) (hhi : N≤67701) :
    Real.log (N : ℝ)≤(11123/1000 : ℝ) := by
  have hn : (N : ℝ)≤67702 := by exact_mod_cast (show N≤67702 by omega)
  exact (Real.log_le_log (by exact_mod_cast (show 0<N by omega)) hn).trans endpoint_log

theorem actual_harmonic {N : ℕ} (hN : 10000≤N) (hhi : N≤67701) :
    Harmonic N≤(23401/2000 : ℝ) := by
  have hh:=HarmonicCaps94488.harmonic_log_5775 hN
  have hl:=actual_log (by omega : 1≤N) hhi
  linarith only [hh,hl]

#print axioms endpoint_log
#print axioms actual_log
#print axioms actual_harmonic
end
end JSP233.Log65968
