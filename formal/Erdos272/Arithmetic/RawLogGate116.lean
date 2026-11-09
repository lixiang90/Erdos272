module

public import Erdos272.Resources.RawEndpoint116
public import Erdos272.Arithmetic.RawLogGate112
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! All-N logarithmic gates for the bootstrap actual r11 width polynomial.
The old polynomial pays only32w<=N; the bootstrap polynomial pays the new
2596/61 restoration or its25/32 profile side. The base log uses a six-term
certified Taylor bound at9/20; the extension uses
an exact polynomial shift certificate against exp. -/
namespace JSP233.RawLogGate116
open StarCompletion APGeometry RawEndpoint112
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem log_400m_tight_lt : Real.log (400000000:ℝ)<19806976/1000000 := by
  have he : (400000000:ℝ)=(2:ℝ)^10*(5:ℝ)^8 := by norm_num
  rw [he,Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  norm_num only [Nat.cast_ofNat]
  linarith only [h2,h5]

theorem log_220m_lt : Real.log (220000000:ℝ)<19217/1000 := by
  have ht := Real.abs_log_sub_add_sum_range_le (x:=(9/20:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at ht
  have hr := (abs_le.mp ht).2
  have he : (220000000:ℝ)=400000000*(11/20:ℝ) := by norm_num
  rw [he,Real.log_mul (by norm_num) (by norm_num)]
  linarith only [hr,log_400m_tight_lt]

theorem coarse_base_rational :
    (32:ℝ)^2*RawPolynomial (19217/1000)<220000000 := by
  norm_num [RawPolynomial]

theorem coarse_base_log :
    (32:ℝ)^2*RawPolynomial (Real.log (220000000:ℝ))≤220000000 := by
  have hl : 0≤Real.log (220000000:ℝ) := Real.log_nonneg (by norm_num)
  have hp := mul_le_mul_of_nonneg_left
    (RawLogGate112.raw_polynomial_monotone hl log_220m_lt.le)
    (by norm_num : (0:ℝ)≤(32:ℝ)^2)
  exact hp.trans coarse_base_rational.le

theorem coarse_gate_real {n : ℝ} (hn : 220000000≤n) :
    (32:ℝ)^2*RawPolynomial (Real.log n)≤n := by
  have hnpos : 0<n := by linarith only [hn]
  have hl : 0≤Real.log (220000000:ℝ) := Real.log_nonneg (by norm_num)
  have hlog : Real.log (220000000:ℝ)≤Real.log n :=
    Real.log_le_log (by norm_num) hn
  have hp := RawLogGate112.raw_polynomial_shift_exp hl (sub_nonneg.mpr hlog)
  have he : Real.log (220000000:ℝ)+(Real.log n-Real.log (220000000:ℝ))=Real.log n := by ring
  have hexp : Real.exp (Real.log n-Real.log (220000000:ℝ))=n/220000000 := by
    rw [Real.exp_sub,Real.exp_log hnpos,Real.exp_log (by norm_num : (0:ℝ)<220000000)]
  rw [he,hexp] at hp
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤(32:ℝ)^2)
  have hb := mul_le_mul_of_nonneg_right coarse_base_log (by positivity : (0:ℝ)≤n/220000000)
  nlinarith only [hm,hb]

theorem actual_preliminary_width_payment {N w : ℕ} (hN : 220000000≤N)
    (hwidth : (w:ℝ)^2≤(N:ℝ)*RawPolynomial (Real.log N)) : 32*w≤N := by
  have hg := coarse_gate_real (n:=(N:ℝ)) (by exact_mod_cast hN)
  have hm := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0:ℝ)≤(32:ℝ)^2)
  have hp := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg N)
  have hs : ((32:ℝ)*(w:ℝ))^2≤(N:ℝ)^2 := by nlinarith only [hm,hp]
  have hl : (32:ℝ)*(w:ℝ)≤(N:ℝ) :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg N)).mp hs
  have hh : (32:ℝ)*(w:ℝ)≤(N:ℝ) := by linarith only [hl]
  exact_mod_cast hh

theorem core_nonnegative {x : ℝ} (hx : 0≤x) : 0≤RawEndpoint116.BootstrapCorePolynomial x := by
  unfold RawEndpoint116.BootstrapCorePolynomial
  positivity

theorem core_monotone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    RawEndpoint116.BootstrapCorePolynomial x≤RawEndpoint116.BootstrapCorePolynomial y := by
  dsimp only [RawEndpoint116.BootstrapCorePolynomial]
  gcongr

theorem core_shift_certificate (x t : ℝ) :
    RawEndpoint116.BootstrapCorePolynomial x*(1+t+t^2/2+t^3/6)-RawEndpoint116.BootstrapCorePolynomial (x+t)=
      (x^3/6+5*x^2+(586/125:ℝ)*x+1111474/62500)*t+
      (x^3/6+11*x^2/2+(1836/125:ℝ)*x+1404474/62500)*t^2/2+
      (x^3/6+11*x^2/2+(1961/125:ℝ)*x+2029474/62500)*t^3/6 := by
  dsimp only [RawEndpoint116.BootstrapCorePolynomial]
  ring

theorem core_shift_exp {x t : ℝ} (hx : 0≤x) (ht : 0≤t) :
    RawEndpoint116.BootstrapCorePolynomial (x+t)≤RawEndpoint116.BootstrapCorePolynomial x*Real.exp t := by
  have hnon : 0≤(x^3/6+5*x^2+(586/125:ℝ)*x+1111474/62500)*t+
      (x^3/6+11*x^2/2+(1836/125:ℝ)*x+1404474/62500)*t^2/2+
      (x^3/6+11*x^2/2+(1961/125:ℝ)*x+2029474/62500)*t^3/6 := by positivity
  have hc : RawEndpoint116.BootstrapCorePolynomial (x+t)≤
      RawEndpoint116.BootstrapCorePolynomial x*(1+t+t^2/2+t^3/6) := by
    have he := core_shift_certificate x t
    linarith only [he,hnon]
  have he : 1+t+t^2/2+t^3/6≤Real.exp t := by
    have hh := Real.sum_le_exp_of_nonneg ht 4
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  exact hc.trans (mul_le_mul_of_nonneg_left he (core_nonnegative hx))

theorem refined_polynomial_monotone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    RawEndpoint116.BootstrapPolynomial x≤RawEndpoint116.BootstrapPolynomial y := by
  exact mul_le_mul_of_nonneg_left (core_monotone hx hxy) (by norm_num)

theorem refined_polynomial_shift_exp {x t : ℝ} (hx : 0≤x) (ht : 0≤t) :
    RawEndpoint116.BootstrapPolynomial (x+t)≤RawEndpoint116.BootstrapPolynomial x*Real.exp t := by
  have hh := mul_le_mul_of_nonneg_left (core_shift_exp hx ht)
    (by norm_num : (0:ℝ)≤114959/3359)
  simpa only [RawEndpoint116.BootstrapPolynomial,mul_assoc] using hh

theorem restore_base_rational :
    (2596/61:ℝ)^2*RawEndpoint116.BootstrapPolynomial (19217/1000)<220000000 := by
  norm_num [RawEndpoint116.BootstrapPolynomial,RawEndpoint116.BootstrapCorePolynomial]

theorem restore_base_log :
    (2596/61:ℝ)^2*RawEndpoint116.BootstrapPolynomial (Real.log (220000000:ℝ))≤220000000 := by
  have hl : 0≤Real.log (220000000:ℝ) := Real.log_nonneg (by norm_num)
  have hp := mul_le_mul_of_nonneg_left (refined_polynomial_monotone hl log_220m_lt.le)
    (by norm_num : (0:ℝ)≤(2596/61:ℝ)^2)
  exact hp.trans restore_base_rational.le

theorem raw_restore_gate_real {n : ℝ} (hn : 220000000≤n) :
    (2596/61:ℝ)^2*RawEndpoint116.BootstrapPolynomial (Real.log n)≤n := by
  have hnpos : 0<n := by linarith only [hn]
  have hl : 0≤Real.log (220000000:ℝ) := Real.log_nonneg (by norm_num)
  have hlog : Real.log (220000000:ℝ)≤Real.log n := Real.log_le_log (by norm_num) hn
  have hp := refined_polynomial_shift_exp hl (sub_nonneg.mpr hlog)
  have he : Real.log (220000000:ℝ)+(Real.log n-Real.log (220000000:ℝ))=Real.log n := by ring
  have hexp : Real.exp (Real.log n-Real.log (220000000:ℝ))=n/220000000 := by
    rw [Real.exp_sub,Real.exp_log hnpos,Real.exp_log (by norm_num : (0:ℝ)<220000000)]
  rw [he,hexp] at hp
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤(2596/61:ℝ)^2)
  have hb := mul_le_mul_of_nonneg_right restore_base_log (by positivity : (0:ℝ)≤n/220000000)
  nlinarith only [hm,hb]

theorem actual_balanced_width_payment {N w : ℕ} (hN : 220000000≤N)
    (hwidth : (w:ℝ)^2≤(N:ℝ)*RawEndpoint116.BootstrapPolynomial (Real.log N)) :
    2596*w≤61*N := by
  have hg := raw_restore_gate_real (n:=(N:ℝ)) (by exact_mod_cast hN)
  have hm := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0:ℝ)≤(2596/61:ℝ)^2)
  have hp := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg N)
  have hs : ((2596/61:ℝ)*(w:ℝ))^2≤(N:ℝ)^2 := by nlinarith only [hm,hp]
  have hl : (2596/61:ℝ)*(w:ℝ)≤(N:ℝ) :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg N)).mp hs
  have hh : (2596:ℝ)*w≤61*(N:ℝ) := by linarith only [hl]
  exact_mod_cast hh

theorem side_restore_gate_real {n : ℝ} (hn : 220000000≤n) :
    (143/3:ℝ)^2*((25/32:ℝ)*RawEndpoint116.BootstrapPolynomial (Real.log n))≤n := by
  have hl : 0≤Real.log n := Real.log_nonneg (by linarith only [hn])
  have hp : 0≤RawEndpoint116.BootstrapPolynomial (Real.log n) := by
    exact mul_nonneg (by norm_num) (core_nonnegative hl)
  have hc : (143/3:ℝ)^2*(25/32:ℝ)≤(2596/61:ℝ)^2 := by norm_num
  have hm := mul_le_mul_of_nonneg_right hc hp
  have he : (143/3:ℝ)^2*((25/32:ℝ)*RawEndpoint116.BootstrapPolynomial (Real.log n))=
      ((143/3:ℝ)^2*(25/32:ℝ))*RawEndpoint116.BootstrapPolynomial (Real.log n) := by ring
  rw [he]
  exact hm.trans (raw_restore_gate_real hn)

theorem actual_unbalanced_width_payment {N w : ℕ} (hN : 220000000≤N)
    (hwidth : (w:ℝ)^2≤(N:ℝ)*((25/32:ℝ)*RawEndpoint116.BootstrapPolynomial (Real.log N))) :
    143*w≤3*N := by
  have hg := side_restore_gate_real (n:=(N:ℝ)) (by exact_mod_cast hN)
  have hm := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0:ℝ)≤(143/3:ℝ)^2)
  have hp := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg N)
  have hs : ((143/3:ℝ)*(w:ℝ))^2≤(N:ℝ)^2 := by nlinarith only [hm,hp]
  have hl : (143/3:ℝ)*(w:ℝ)≤(N:ℝ) :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg N)).mp hs
  have hh : (143:ℝ)*w≤3*(N:ℝ) := by linarith only [hl]
  exact_mod_cast hh

#print axioms log_400m_tight_lt
#print axioms log_220m_lt
#print axioms coarse_base_rational
#print axioms coarse_base_log
#print axioms coarse_gate_real
#print axioms actual_preliminary_width_payment
#print axioms core_nonnegative
#print axioms core_monotone
#print axioms core_shift_certificate
#print axioms core_shift_exp
#print axioms refined_polynomial_monotone
#print axioms refined_polynomial_shift_exp
#print axioms restore_base_rational
#print axioms restore_base_log
#print axioms raw_restore_gate_real
#print axioms actual_balanced_width_payment
#print axioms side_restore_gate_real
#print axioms actual_unbalanced_width_payment
end
end JSP233.RawLogGate116
