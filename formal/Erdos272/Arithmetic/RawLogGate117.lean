module

public import Erdos272.Arithmetic.RawLogGate116
public import Erdos272.Arithmetic.RawLogGate112
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! The191m all-N arithmetic gate uses the old unconditional32-width
preparation and the same bootstrap polynomial with final restoration ratio40.
The actual quadratic profile is normalized at1600 without a side branch. -/
namespace JSP233.RawLogGate117
open StarCompletion APGeometry RawEndpoint112
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem log_200m_tight_lt : Real.log (200000000:ℝ)<19113828/1000000 := by
  have he : (200000000:ℝ)=(2:ℝ)^9*(5:ℝ)^8 := by norm_num
  rw [he,Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  norm_num only [Nat.cast_ofNat]
  linarith only [h2,h5]

theorem log_191m_lt : Real.log (191000000:ℝ)<95339/5000 := by
  have ht := Real.abs_log_sub_add_sum_range_le (x:=(9/200:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at ht
  have hr := (abs_le.mp ht).2
  have he : (191000000:ℝ)=200000000*(191/200:ℝ) := by norm_num
  rw [he,Real.log_mul (by norm_num) (by norm_num)]
  linarith only [hr,log_200m_tight_lt]

theorem coarse_base_rational :
    (32:ℝ)^2*RawPolynomial (95339/5000)<191000000 := by
  norm_num [RawPolynomial]

theorem coarse_base_log :
    (32:ℝ)^2*RawPolynomial (Real.log (191000000:ℝ))≤191000000 := by
  have hl : 0≤Real.log (191000000:ℝ) := Real.log_nonneg (by norm_num)
  have hp := mul_le_mul_of_nonneg_left
    (RawLogGate112.raw_polynomial_monotone hl log_191m_lt.le)
    (by norm_num : (0:ℝ)≤(32:ℝ)^2)
  exact hp.trans coarse_base_rational.le

theorem coarse_gate_real {n : ℝ} (hn : 191000000≤n) :
    (32:ℝ)^2*RawPolynomial (Real.log n)≤n := by
  have hnpos : 0<n := by linarith only [hn]
  have hl : 0≤Real.log (191000000:ℝ) := Real.log_nonneg (by norm_num)
  have hlog : Real.log (191000000:ℝ)≤Real.log n :=
    Real.log_le_log (by norm_num) hn
  have hp := RawLogGate112.raw_polynomial_shift_exp hl (sub_nonneg.mpr hlog)
  have he : Real.log (191000000:ℝ)+(Real.log n-Real.log (191000000:ℝ))=Real.log n := by ring
  have hexp : Real.exp (Real.log n-Real.log (191000000:ℝ))=n/191000000 := by
    rw [Real.exp_sub,Real.exp_log hnpos,Real.exp_log (by norm_num : (0:ℝ)<191000000)]
  rw [he,hexp] at hp
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤(32:ℝ)^2)
  have hb := mul_le_mul_of_nonneg_right coarse_base_log (by positivity : (0:ℝ)≤n/191000000)
  nlinarith only [hm,hb]

theorem actual_preliminary_width_payment {N w : ℕ} (hN : 191000000≤N)
    (hwidth : (w:ℝ)^2≤(N:ℝ)*RawPolynomial (Real.log N)) : 32*w≤N := by
  have hg := coarse_gate_real (n:=(N:ℝ)) (by exact_mod_cast hN)
  have hm := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0:ℝ)≤(32:ℝ)^2)
  have hp := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg N)
  have hs : ((32:ℝ)*(w:ℝ))^2≤(N:ℝ)^2 := by nlinarith only [hm,hp]
  have hl : (32:ℝ)*(w:ℝ)≤(N:ℝ) :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg N)).mp hs
  have hh : (32:ℝ)*(w:ℝ)≤(N:ℝ) := by linarith only [hl]
  exact_mod_cast hh

theorem restore_base_rational :
    (40:ℝ)^2*RawEndpoint116.BootstrapPolynomial (95339/5000)<191000000 := by
  norm_num [RawEndpoint116.BootstrapPolynomial,RawEndpoint116.BootstrapCorePolynomial]

theorem restore_base_log :
    (40:ℝ)^2*RawEndpoint116.BootstrapPolynomial (Real.log (191000000:ℝ))≤191000000 := by
  have hl : 0≤Real.log (191000000:ℝ) := Real.log_nonneg (by norm_num)
  have hp := mul_le_mul_of_nonneg_left (RawLogGate116.refined_polynomial_monotone hl log_191m_lt.le)
    (by norm_num : (0:ℝ)≤(40:ℝ)^2)
  exact hp.trans restore_base_rational.le

theorem raw_restore_gate_real {n : ℝ} (hn : 191000000≤n) :
    (40:ℝ)^2*RawEndpoint116.BootstrapPolynomial (Real.log n)≤n := by
  have hnpos : 0<n := by linarith only [hn]
  have hl : 0≤Real.log (191000000:ℝ) := Real.log_nonneg (by norm_num)
  have hlog : Real.log (191000000:ℝ)≤Real.log n := Real.log_le_log (by norm_num) hn
  have hp := RawLogGate116.refined_polynomial_shift_exp hl (sub_nonneg.mpr hlog)
  have he : Real.log (191000000:ℝ)+(Real.log n-Real.log (191000000:ℝ))=Real.log n := by ring
  have hexp : Real.exp (Real.log n-Real.log (191000000:ℝ))=n/191000000 := by
    rw [Real.exp_sub,Real.exp_log hnpos,Real.exp_log (by norm_num : (0:ℝ)<191000000)]
  rw [he,hexp] at hp
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤(40:ℝ)^2)
  have hb := mul_le_mul_of_nonneg_right restore_base_log (by positivity : (0:ℝ)≤n/191000000)
  nlinarith only [hm,hb]

theorem actual_balanced_width_payment {N w : ℕ} (hN : 191000000≤N)
    (hwidth : (w:ℝ)^2≤(N:ℝ)*RawEndpoint116.BootstrapPolynomial (Real.log N)) :
    40*w≤N := by
  have hg := raw_restore_gate_real (n:=(N:ℝ)) (by exact_mod_cast hN)
  have hm := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0:ℝ)≤(40:ℝ)^2)
  have hp := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg N)
  have hs : ((40:ℝ)*(w:ℝ))^2≤(N:ℝ)^2 := by nlinarith only [hm,hp]
  have hl : (40:ℝ)*(w:ℝ)≤(N:ℝ) :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg N)).mp hs
  have hh : (40:ℝ)*w≤(N:ℝ) := by linarith only [hl]
  exact_mod_cast hh

theorem actual_bootstrap_profile_payment {N : ℕ} {D : ℝ} (hN : 191000000≤N)
    (hprofile : D≤(N:ℝ)*RawEndpoint116.BootstrapCorePolynomial (Real.log N)) :
    1600*D≤DeficitCoeff*(N:ℝ)^2 := by
  have hg := raw_restore_gate_real (n:=(N:ℝ)) (by exact_mod_cast hN)
  have hc : 1600*RawEndpoint116.BootstrapCorePolynomial (Real.log N)≤DeficitCoeff*(N:ℝ) := by
    dsimp only [RawEndpoint116.BootstrapPolynomial,DeficitCoeff] at *
    nlinarith only [hg]
  have hm := mul_le_mul_of_nonneg_left hprofile (by norm_num : (0:ℝ)≤1600)
  have hp := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg N)
  nlinarith only [hm,hp]

#print axioms log_200m_tight_lt
#print axioms log_191m_lt
#print axioms coarse_base_rational
#print axioms coarse_base_log
#print axioms coarse_gate_real
#print axioms actual_preliminary_width_payment
#print axioms restore_base_rational
#print axioms restore_base_log
#print axioms raw_restore_gate_real
#print axioms actual_balanced_width_payment
#print axioms actual_bootstrap_profile_payment
end
end JSP233.RawLogGate117
