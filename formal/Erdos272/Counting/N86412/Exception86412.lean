module

public import Erdos272.Resources.N86412.LocalRecovery86412
public import Erdos272.Arithmetic.SimplexMoment57

@[expose] public section

namespace JSP233.Exception86412
open StarCompletion APGeometry WitnessInterval43 RestrictedWitness44 HarmonicAbel29 HarmonicLog55
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem exception_cap {N : ℕ} {c : ℤ} (hN : 10000≤N) (hhi : N≤88403)
    (hc : c∈Ground N) : (WitnessException (Ground N) c : ℝ)≤1001*N := by
  have caps := LocalRecovery86412.actual_caps (k := 0) (by decide) hN hhi
  have hell : Real.log (N : ℝ)≤1139/100 := by
    simpa [LocalRecovery86412.LogLocal] using caps.log_le
  have hh : Harmonic N≤12 := by
    have ht := caps.harmonic_le
    norm_num [LocalRecovery86412.HLocal, LocalRecovery86412.LogLocal] at ht
    exact ht
  have hlog : 0≤Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have h := SimplexMoment57.actual_simplex_exception hc
  have hp : SimplexPolynomial (Real.log N) (Harmonic N)≤SimplexPolynomial (1139/100) 12 := by
    dsimp only [SimplexPolynomial]
    gcongr
  have hpay := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) N)
  norm_num [SimplexPolynomial] at hpay
  dsimp only [SimplexPolynomial] at h
  nlinarith only [h, hpay, Nat.cast_nonneg (α := ℝ) N]

#print axioms exception_cap
end
end JSP233.Exception86412
