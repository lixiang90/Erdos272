module

public import Erdos272.Resources.N86412.LocalRecovery86412

@[expose] public section

namespace JSP233.Harmonic82427
open HarmonicAbel29
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_cap {N : ℕ} (hN : 10000≤N) (hhi : N≤84363) :
    Harmonic N≤(11921/1000 : ℝ) := by
  have hn : (N : ℝ)≤84363 := by exact_mod_cast hhi
  have hlog := LocalRecovery86412.log_anchor
    (show (0 : ℝ)<N by exact_mod_cast (show 0<N by omega))
  have hh := HarmonicCaps94488.harmonic_log_5775 hN
  have h2 := LogThree126.log_two_window.2
  have h3 := LogThree126.log_three_window.1
  have hpay : 18*LogThree126.TwoHi-LogThree126.ThreeLo+
      (3*(84363 : ℝ)-262144)/262144+231/400≤11921/1000 := by
    norm_num [LogThree126.TwoHi, LogThree126.ThreeLo]
  linarith only [hn, hlog, hh, h2, h3, hpay]

#print axioms actual_cap
end JSP233.Harmonic82427
