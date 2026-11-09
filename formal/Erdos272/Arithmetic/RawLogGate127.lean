module

public import Erdos272.Resources.RawEndpoint127
public import Erdos272.Resources.CoarseEndpoint127
public import Erdos272.Arithmetic.RawLogGate117
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! The113.113m gates retain the complete absolute exclusion tangent fee. The fine
core has a negative constant; positivity and exponential shift are proved
only for x at least11. The fee is paid separately under the squared anchor
ratio, and never absorbed into an unproved asymptotic constant. -/
namespace JSP233.RawLogGate127
open StarCompletion APGeometry RawEndpoint112
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem log_113p113m_lt : Real.log (113113000:ℝ)<185439/10000 := by
  have ht := Real.abs_log_sub_add_sum_range_le (x:=(86887/200000:ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at ht
  have hr := (abs_le.mp ht).2
  have he : (113113000:ℝ)=200000000*(113113/200000:ℝ) := by norm_num
  rw [he,Real.log_mul (by norm_num) (by norm_num)]
  linarith only [hr,RawLogGate117.log_200m_tight_lt]

theorem core_nonnegative {x : ℝ} (hx : 11≤x) : 0≤RawEndpoint127.BootstrapCorePolynomial x := by
  have hx0 : 0≤x := by linarith only [hx]
  have hx2 := sq_nonneg x
  have hx3 : 0≤x^3 := pow_nonneg hx0 3
  dsimp only [RawEndpoint127.BootstrapCorePolynomial]
  nlinarith only [hx,hx2,hx3]

theorem core_monotone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    RawEndpoint127.BootstrapCorePolynomial x≤RawEndpoint127.BootstrapCorePolynomial y := by
  dsimp only [RawEndpoint127.BootstrapCorePolynomial]
  gcongr

theorem core_shift_certificate (x t : ℝ) :
    RawEndpoint127.BootstrapCorePolynomial x*(1+t+t^2/2+t^3/6)-RawEndpoint127.BootstrapCorePolynomial (x+t)=
      (x^3/6+(241/100)*x^2+(93381/10000)*x-24328285/100000)*t+
      (x^3/6+(291/100)*x^2+(141581/10000)*x-23394475/100000)*t^2/2+
      (x^3/6+(291/100)*x^2+(151581/10000)*x-22912475/100000)*t^3/6 := by
  dsimp only [RawEndpoint127.BootstrapCorePolynomial]
  ring

theorem core_shift_exp {x t : ℝ} (hx : 11≤x) (ht : 0≤t) :
    RawEndpoint127.BootstrapCorePolynomial (x+t)≤RawEndpoint127.BootstrapCorePolynomial x*Real.exp t := by
  have hx0 : 0≤x := by linarith only [hx]
  have hx2 := sq_nonneg x
  have hx3 : 0≤x^3 := pow_nonneg hx0 3
  have hA : 0≤x^3/6+(241/100)*x^2+(93381/10000)*x-24328285/100000 := by
    nlinarith only [hx,hx2,hx3]
  have hB : 0≤x^3/6+(291/100)*x^2+(141581/10000)*x-23394475/100000 := by
    nlinarith only [hx,hx2,hx3]
  have hC : 0≤x^3/6+(291/100)*x^2+(151581/10000)*x-22912475/100000 := by
    nlinarith only [hx,hx2,hx3]
  have hnon : 0≤(x^3/6+(241/100)*x^2+(93381/10000)*x-24328285/100000)*t+
      (x^3/6+(291/100)*x^2+(141581/10000)*x-23394475/100000)*t^2/2+
      (x^3/6+(291/100)*x^2+(151581/10000)*x-22912475/100000)*t^3/6 := by positivity
  have hc : RawEndpoint127.BootstrapCorePolynomial (x+t)≤
      RawEndpoint127.BootstrapCorePolynomial x*(1+t+t^2/2+t^3/6) := by
    have he := core_shift_certificate x t
    linarith only [he,hnon]
  have he : 1+t+t^2/2+t^3/6≤Real.exp t := by
    have hh := Real.sum_le_exp_of_nonneg ht 4
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  exact hc.trans (mul_le_mul_of_nonneg_left he (core_nonnegative hx))

theorem refined_polynomial_monotone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    RawEndpoint127.BootstrapPolynomial x≤RawEndpoint127.BootstrapPolynomial y := by
  exact mul_le_mul_of_nonneg_left (core_monotone hx hxy) (by norm_num)

theorem refined_polynomial_shift_exp {x t : ℝ} (hx : 11≤x) (ht : 0≤t) :
    RawEndpoint127.BootstrapPolynomial (x+t)≤RawEndpoint127.BootstrapPolynomial x*Real.exp t := by
  have hh := mul_le_mul_of_nonneg_left (core_shift_exp hx ht)
    (by norm_num : (0:ℝ)≤114959/3359)
  simpa only [RawEndpoint127.BootstrapPolynomial,mul_assoc] using hh

theorem base_log_lower11 : 11≤Real.log (113113000:ℝ) := by
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<65536)
    (by norm_num : (65536:ℝ)≤113113000)
  have he : (65536:ℝ)=(2:ℝ)^16 := by norm_num
  rw [he,Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl,HarmonicLog55.actual_log_two_lower]

theorem coarse_polynomial_monotone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    CoarseEndpoint127.CoarsePolynomial x≤CoarseEndpoint127.CoarsePolynomial y := by
  have hh := core_monotone hx hxy
  dsimp only [CoarseEndpoint127.CoarsePolynomial,CoarseEndpoint127.CoarseCorePolynomial]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  linarith only [hh]

theorem coarse_polynomial_shift_exp {x t : ℝ} (hx : 11≤x) (ht : 0≤t) :
    CoarseEndpoint127.CoarsePolynomial (x+t)≤CoarseEndpoint127.CoarsePolynomial x*Real.exp t := by
  have hp := core_shift_exp hx ht
  have he : 1≤Real.exp t := Real.one_le_exp ht
  have hh : CoarseEndpoint127.CoarseCorePolynomial (x+t)≤
      CoarseEndpoint127.CoarseCorePolynomial x*Real.exp t := by
    dsimp only [CoarseEndpoint127.CoarseCorePolynomial]
    nlinarith only [hp,he]
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤114959/3359)
  simpa only [CoarseEndpoint127.CoarsePolynomial,mul_assoc] using hm

theorem coarse_base_rational :
    (32:ℝ)^2*(113113000*CoarseEndpoint127.CoarsePolynomial (185439/10000)+
      (114959/3359:ℝ)*WitnessSingle127.FullFee)<(113113000:ℝ)^2 := by
  norm_num [CoarseEndpoint127.CoarsePolynomial,CoarseEndpoint127.CoarseCorePolynomial,RawEndpoint127.BootstrapCorePolynomial,
    WitnessSingle127.FullFee,SingleTangent127.Intercept,LogAnchor127.AnchorIntercept]

theorem coarse_base_log :
    (32:ℝ)^2*(113113000*CoarseEndpoint127.CoarsePolynomial (Real.log (113113000:ℝ))+
      (114959/3359:ℝ)*WitnessSingle127.FullFee)≤(113113000:ℝ)^2 := by
  have hl : 0≤Real.log (113113000:ℝ) := Real.log_nonneg (by norm_num)
  have hp := mul_le_mul_of_nonneg_left (coarse_polynomial_monotone hl log_113p113m_lt.le)
    (by norm_num : (0:ℝ)≤(32:ℝ)^2*113113000)
  nlinarith only [hp,coarse_base_rational.le]

theorem coarse_gate_real {n : ℝ} (hn : 113113000≤n) :
    (32:ℝ)^2*(n*CoarseEndpoint127.CoarsePolynomial (Real.log n)+
      (114959/3359:ℝ)*WitnessSingle127.FullFee)≤n^2 := by
  have hnpos : 0<n := by linarith only [hn]
  have hlog : Real.log (113113000:ℝ)≤Real.log n := Real.log_le_log (by norm_num) hn
  have hp := coarse_polynomial_shift_exp base_log_lower11 (sub_nonneg.mpr hlog)
  have he : Real.log (113113000:ℝ)+(Real.log n-Real.log (113113000:ℝ))=Real.log n := by ring
  have hexp : Real.exp (Real.log n-Real.log (113113000:ℝ))=n/113113000 := by
    rw [Real.exp_sub,Real.exp_log hnpos,Real.exp_log (by norm_num : (0:ℝ)<113113000)]
  rw [he,hexp] at hp
  let y : ℝ := n/113113000
  have hy : 1≤y := by dsimp only [y];linarith only [hn]
  have hy2 : 1≤y^2 := by nlinarith only [hy,sq_nonneg (y-1)]
  have hny : n=113113000*y := by dsimp only [y];ring
  have hpoly : n*CoarseEndpoint127.CoarsePolynomial (Real.log n)≤
      113113000*CoarseEndpoint127.CoarsePolynomial (Real.log (113113000:ℝ))*y^2 := by
    calc
      _≤n*(CoarseEndpoint127.CoarsePolynomial (Real.log (113113000:ℝ))*y) :=
        mul_le_mul_of_nonneg_left hp hnpos.le
      _=_ := by rw [hny];ring
  have hf0 : (0:ℝ)≤(114959/3359:ℝ)*WitnessSingle127.FullFee := by
    norm_num [WitnessSingle127.FullFee,SingleTangent127.Intercept,LogAnchor127.AnchorIntercept]
  have hf : (114959/3359:ℝ)*WitnessSingle127.FullFee≤
      ((114959/3359:ℝ)*WitnessSingle127.FullFee)*y^2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy2 hf0
  have hsum : (32:ℝ)^2*(n*CoarseEndpoint127.CoarsePolynomial (Real.log n)+
      (114959/3359:ℝ)*WitnessSingle127.FullFee)≤
      ((32:ℝ)^2*(113113000*CoarseEndpoint127.CoarsePolynomial (Real.log (113113000:ℝ))+
        (114959/3359:ℝ)*WitnessSingle127.FullFee))*y^2 := by
    nlinarith only [hpoly,hf]
  have hb := mul_le_mul_of_nonneg_right coarse_base_log (sq_nonneg y)
  calc
    _≤_ := hsum
    _≤(113113000:ℝ)^2*y^2 := hb
    _=n^2 := by rw [hny];ring

theorem actual_preliminary_width_payment {N w : ℕ} (hN : 113113000≤N)
    (hwidth : (w:ℝ)^2≤(N:ℝ)*CoarseEndpoint127.CoarsePolynomial (Real.log N)+
      (114959/3359:ℝ)*WitnessSingle127.FullFee) : 32*w≤N := by
  have hg := coarse_gate_real (n:=(N:ℝ)) (by exact_mod_cast hN)
  have hm := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0:ℝ)≤(32:ℝ)^2)
  have hs : ((32:ℝ)*(w:ℝ))^2≤(N:ℝ)^2 := by nlinarith only [hm,hg]
  have hl : (32:ℝ)*(w:ℝ)≤(N:ℝ) :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg N)).mp hs
  exact_mod_cast hl

theorem restore_base_rational :
    (900/23:ℝ)^2*(113113000*RawEndpoint127.BootstrapPolynomial (185439/10000)+
      (114959/3359:ℝ)*WitnessSingle127.FullFee)<(113113000:ℝ)^2 := by
  norm_num [RawEndpoint127.BootstrapPolynomial,RawEndpoint127.BootstrapCorePolynomial,
    WitnessSingle127.FullFee,SingleTangent127.Intercept,LogAnchor127.AnchorIntercept]

theorem restore_base_log :
    (900/23:ℝ)^2*(113113000*RawEndpoint127.BootstrapPolynomial (Real.log (113113000:ℝ))+
      (114959/3359:ℝ)*WitnessSingle127.FullFee)≤(113113000:ℝ)^2 := by
  have hl : 0≤Real.log (113113000:ℝ) := Real.log_nonneg (by norm_num)
  have hp := mul_le_mul_of_nonneg_left (refined_polynomial_monotone hl log_113p113m_lt.le)
    (by norm_num : (0:ℝ)≤(900/23:ℝ)^2*113113000)
  nlinarith only [hp,restore_base_rational.le]

theorem raw_restore_gate_real {n : ℝ} (hn : 113113000≤n) :
    (900/23:ℝ)^2*(n*RawEndpoint127.BootstrapPolynomial (Real.log n)+
      (114959/3359:ℝ)*WitnessSingle127.FullFee)≤n^2 := by
  have hnpos : 0<n := by linarith only [hn]
  have hlog : Real.log (113113000:ℝ)≤Real.log n := Real.log_le_log (by norm_num) hn
  have hp := refined_polynomial_shift_exp base_log_lower11 (sub_nonneg.mpr hlog)
  have he : Real.log (113113000:ℝ)+(Real.log n-Real.log (113113000:ℝ))=Real.log n := by ring
  have hexp : Real.exp (Real.log n-Real.log (113113000:ℝ))=n/113113000 := by
    rw [Real.exp_sub,Real.exp_log hnpos,Real.exp_log (by norm_num : (0:ℝ)<113113000)]
  rw [he,hexp] at hp
  let y : ℝ := n/113113000
  have hy : 1≤y := by dsimp only [y];linarith only [hn]
  have hy2 : 1≤y^2 := by nlinarith only [hy,sq_nonneg (y-1)]
  have hny : n=113113000*y := by dsimp only [y];ring
  have hpoly : n*RawEndpoint127.BootstrapPolynomial (Real.log n)≤
      113113000*RawEndpoint127.BootstrapPolynomial (Real.log (113113000:ℝ))*y^2 := by
    calc
      _≤n*(RawEndpoint127.BootstrapPolynomial (Real.log (113113000:ℝ))*y) :=
        mul_le_mul_of_nonneg_left hp hnpos.le
      _=_ := by rw [hny];ring
  have hf0 : (0:ℝ)≤(114959/3359:ℝ)*WitnessSingle127.FullFee := by
    norm_num [WitnessSingle127.FullFee,SingleTangent127.Intercept,LogAnchor127.AnchorIntercept]
  have hf : (114959/3359:ℝ)*WitnessSingle127.FullFee≤
      ((114959/3359:ℝ)*WitnessSingle127.FullFee)*y^2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy2 hf0
  have hsum : (900/23:ℝ)^2*(n*RawEndpoint127.BootstrapPolynomial (Real.log n)+
      (114959/3359:ℝ)*WitnessSingle127.FullFee)≤
      ((900/23:ℝ)^2*(113113000*RawEndpoint127.BootstrapPolynomial (Real.log (113113000:ℝ))+
        (114959/3359:ℝ)*WitnessSingle127.FullFee))*y^2 := by
    nlinarith only [hpoly,hf]
  have hb := mul_le_mul_of_nonneg_right restore_base_log (sq_nonneg y)
  calc
    _≤_ := hsum
    _≤(113113000:ℝ)^2*y^2 := hb
    _=n^2 := by rw [hny];ring

theorem actual_balanced_width_payment {N w : ℕ} (hN : 113113000≤N)
    (hwidth : (w:ℝ)^2≤(N:ℝ)*RawEndpoint127.BootstrapPolynomial (Real.log N)+
      (114959/3359:ℝ)*WitnessSingle127.FullFee) : 900*w≤23*N := by
  have hg := raw_restore_gate_real (n:=(N:ℝ)) (by exact_mod_cast hN)
  have hm := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0:ℝ)≤(900/23:ℝ)^2)
  have hs : ((900/23:ℝ)*(w:ℝ))^2≤(N:ℝ)^2 := by nlinarith only [hm,hg]
  have hl : (900/23:ℝ)*(w:ℝ)≤(N:ℝ) :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg N)).mp hs
  have hh : (900:ℝ)*w≤23*(N:ℝ) := by linarith only [hl]
  exact_mod_cast hh

theorem actual_bootstrap_profile_payment {N : ℕ} {D : ℝ} (hN : 113113000≤N)
    (hprofile : D≤(N:ℝ)*RawEndpoint127.BootstrapCorePolynomial (Real.log N)+WitnessSingle127.FullFee) :
    810000*D≤529*DeficitCoeff*(N:ℝ)^2 := by
  have hg := raw_restore_gate_real (n:=(N:ℝ)) (by exact_mod_cast hN)
  have hc : 810000*((N:ℝ)*RawEndpoint127.BootstrapCorePolynomial (Real.log N)+WitnessSingle127.FullFee)≤
      529*DeficitCoeff*(N:ℝ)^2 := by
    dsimp only [RawEndpoint127.BootstrapPolynomial,DeficitCoeff] at hg ⊢
    nlinarith only [hg]
  exact (mul_le_mul_of_nonneg_left hprofile (by norm_num : (0:ℝ)≤810000)).trans hc

#print axioms log_113p113m_lt
#print axioms core_nonnegative
#print axioms core_monotone
#print axioms core_shift_certificate
#print axioms core_shift_exp
#print axioms refined_polynomial_monotone
#print axioms refined_polynomial_shift_exp
#print axioms base_log_lower11
#print axioms coarse_polynomial_monotone
#print axioms coarse_polynomial_shift_exp
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
end JSP233.RawLogGate127
