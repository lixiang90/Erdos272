module

public import Erdos272.Resources.RawEndpoint112
public import Erdos272.Retention.Restore11Ratio112
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
All-N logarithmic payment for the existing actual r11 ratio restore theorem.
The cubic divided by exp is nonincreasing on the nonnegative real line:
this is proved by an exact coefficient comparison with the four-term exp
series, not by checking a numerical range.  The only numerical base is a
kernel-rational calculation and the Mathlib bounds for log 2 and log 5.
-/
namespace JSP233.RawLogGate112
open StarCompletion APGeometry RawEndpoint112 Restore11Ratio112
open DenseDeletion40 LongTerminal35
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def CorePolynomial (x : ℝ) : ℝ := x^3/6+11*x^2/2+19*x+527

theorem core_nonnegative {x : ℝ} (hx : 0≤x) : 0≤CorePolynomial x := by
  unfold CorePolynomial
  positivity

theorem core_monotone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    CorePolynomial x≤CorePolynomial y := by
  dsimp only [CorePolynomial]
  gcongr

theorem core_shift_certificate (x t : ℝ) :
    CorePolynomial x*(1+t+t^2/2+t^3/6)-CorePolynomial (x+t)=
      (x^3/6+5*x^2+8*x+508)*t+
      (x^3/6+11*x^2/2+18*x+516)*t^2/2+
      (x^3/6+11*x^2/2+19*x+526)*t^3/6 := by
  dsimp only [CorePolynomial]
  ring

theorem core_shift_exp {x t : ℝ} (hx : 0≤x) (ht : 0≤t) :
    CorePolynomial (x+t)≤CorePolynomial x*Real.exp t := by
  have hnon : 0≤(x^3/6+5*x^2+8*x+508)*t+
      (x^3/6+11*x^2/2+18*x+516)*t^2/2+
      (x^3/6+11*x^2/2+19*x+526)*t^3/6 := by positivity
  have hc : CorePolynomial (x+t)≤CorePolynomial x*(1+t+t^2/2+t^3/6) := by
    have he := core_shift_certificate x t
    linarith only [he,hnon]
  have he : 1+t+t^2/2+t^3/6≤Real.exp t := by
    have hh := Real.sum_le_exp_of_nonneg ht 4
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  exact hc.trans (mul_le_mul_of_nonneg_left he (core_nonnegative hx))

theorem raw_polynomial_monotone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    RawPolynomial x≤RawPolynomial y := by
  have hh := mul_le_mul_of_nonneg_left (core_monotone hx hxy)
    (by norm_num : (0:ℝ)≤114959/3359)
  simpa only [RawPolynomial,CorePolynomial] using hh

theorem raw_polynomial_shift_exp {x t : ℝ} (hx : 0≤x) (ht : 0≤t) :
    RawPolynomial (x+t)≤RawPolynomial x*Real.exp t := by
  have hh := mul_le_mul_of_nonneg_left (core_shift_exp hx ht)
    (by norm_num : (0:ℝ)≤114959/3359)
  simpa only [RawPolynomial,CorePolynomial,mul_assoc] using hh

theorem log_400m_lt : Real.log (400000000:ℝ)<1981/100 := by
  have he : (400000000:ℝ)=(2:ℝ)^10*(5:ℝ)^8 := by norm_num
  rw [he,Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  norm_num only [Nat.cast_ofNat]
  linarith only [h2,h5]

theorem restore_base_rational :
    (154/3:ℝ)^2*RawPolynomial (1981/100)<400000000 := by
  norm_num [RawPolynomial]

theorem restore_base_log :
    (154/3:ℝ)^2*RawPolynomial (Real.log (400000000:ℝ))≤400000000 := by
  have hl : 0≤Real.log (400000000:ℝ) := Real.log_nonneg (by norm_num)
  have hp := mul_le_mul_of_nonneg_left (raw_polynomial_monotone hl log_400m_lt.le)
    (by norm_num : (0:ℝ)≤(154/3:ℝ)^2)
  exact hp.trans restore_base_rational.le

theorem raw_restore_gate_real {n : ℝ} (hn : 400000000≤n) :
    (154/3:ℝ)^2*RawPolynomial (Real.log n)≤n := by
  have hnpos : 0<n := by linarith only [hn]
  have hl : 0≤Real.log (400000000:ℝ) := Real.log_nonneg (by norm_num)
  have hlog : Real.log (400000000:ℝ)≤Real.log n :=
    Real.log_le_log (by norm_num) hn
  have hp := raw_polynomial_shift_exp hl (sub_nonneg.mpr hlog)
  have he : Real.log (400000000:ℝ)+(Real.log n-Real.log (400000000:ℝ))=Real.log n := by ring
  have hexp : Real.exp (Real.log n-Real.log (400000000:ℝ))=n/400000000 := by
    rw [Real.exp_sub,Real.exp_log hnpos,Real.exp_log (by norm_num : (0:ℝ)<400000000)]
  rw [he,hexp] at hp
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤(154/3:ℝ)^2)
  have hb := mul_le_mul_of_nonneg_right restore_base_log (by positivity : (0:ℝ)≤n/400000000)
  nlinarith only [hm,hb]

theorem raw_restore_gate {N : ℕ} (hN : 400000000≤N) :
    (154/3:ℝ)^2*RawPolynomial (Real.log N)≤N :=
  raw_restore_gate_real (by exact_mod_cast hN)

theorem actual_ratio11_width_payment {N w : ℕ} (hN : 400000000≤N)
    (hwidth : (w:ℝ)^2≤(N:ℝ)*RawPolynomial (Real.log N)) : 154*w≤3*N := by
  have hg := raw_restore_gate hN
  have hm := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0:ℝ)≤(154/3:ℝ)^2)
  have hp := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg N)
  have hs : ((154/3:ℝ)*(w:ℝ))^2≤(N:ℝ)^2 := by nlinarith only [hm,hp]
  have hl : (154/3:ℝ)*(w:ℝ)≤(N:ℝ) :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg N)).mp hs
  have hh : (154:ℝ)*w≤3*(N:ℝ) := by linarith only [hl]
  exact_mod_cast hh

theorem actual_deleted_avoider_restore11_of_raw
    (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : 400000000≤N) (hNu : N<2^50)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hwidth : ((L:ℝ)+(N-R))^2≤(N:ℝ)*RawPolynomial (Real.log N))
    (hlegal : Legal (Ground N) F)
    (hne : (Avoiders (Retained N 11 F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  have he : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N-R) := by
    rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add]
    ring
  have hw : ((L+N-R:ℕ):ℝ)^2≤(N:ℝ)*RawPolynomial (Real.log N) := by rwa [he]
  exact actual_deleted_avoider_restore11_ratio N c L R F hNu
    (by norm_num;omega) hc hcL hLR hRN (actual_ratio11_width_payment hN hw) hlegal hne hi

#print axioms core_nonnegative
#print axioms core_monotone
#print axioms core_shift_certificate
#print axioms core_shift_exp
#print axioms raw_polynomial_monotone
#print axioms raw_polynomial_shift_exp
#print axioms log_400m_lt
#print axioms restore_base_rational
#print axioms restore_base_log
#print axioms raw_restore_gate_real
#print axioms raw_restore_gate
#print axioms actual_ratio11_width_payment
#print axioms actual_deleted_avoider_restore11_of_raw
end
end JSP233.RawLogGate112
