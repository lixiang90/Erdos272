module

public import Erdos272.Arithmetic.RawLogGate127

@[expose] public section
namespace JSP233.DirectGate128
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def P (x : ℝ) : ℝ := (8/75)*x^3+(3428213/1000000)*x^2+(13405041/1000000)*x+7951327/200000
def Pc (x : ℝ) : ℝ := P x+9677/20
def Rho : ℝ := 114959/3359

theorem log_base_upper : Real.log (112456000:ℝ)<18538073/1000000 := by
  have ht := Real.abs_log_sub_add_sum_range_le (x:=(10943/25000:ℝ)) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at ht
  have hr := (abs_le.mp ht).2
  have he : (112456000:ℝ)=200000000*(14057/25000:ℝ) := by norm_num
  rw [he,Real.log_mul (by norm_num) (by norm_num)]
  linarith only [hr,JSP233.RawLogGate117.log_200m_tight_lt]

theorem p_nonnegative {x : ℝ} (hx : 0≤x) : 0≤P x := by
  dsimp only [P]
  positivity

theorem p_monotone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) : P x≤P y := by
  dsimp only [P]
  gcongr

theorem p_shift_certificate (x t : ℝ) :
    P x*(1+t+t^2/2+t^3/6)-P (x+t)=
      ((8/75)*x^3+(3108213/1000000)*x^2+(6548615/1000000)*x+26351594/1000000)*t+
      ((8/75)*x^3+(3428213/1000000)*x^2+(12765041/1000000)*x+32900209/1000000)*t^2/2+
      ((8/75)*x^3+(3428213/1000000)*x^2+(13405041/1000000)*x+39116635/1000000)*t^3/6 := by
  dsimp only [P]
  ring

theorem p_shift_exp {x t : ℝ} (hx : 0≤x) (ht : 0≤t) : P (x+t)≤P x*Real.exp t := by
  have hp := p_shift_certificate x t
  have he : 0≤P x*(1+t+t^2/2+t^3/6)-P (x+t) := by
    rw [hp]
    positivity
  have hb : 1+t+t^2/2+t^3/6≤Real.exp t := by
    have hh := Real.sum_le_exp_of_nonneg ht 4
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  have hl : P (x+t)≤P x*(1+t+t^2/2+t^3/6) := by linarith only [he]
  exact hl.trans (mul_le_mul_of_nonneg_left hb (p_nonnegative hx))

theorem pc_monotone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) : Pc x≤Pc y :=
  by
    dsimp only [Pc]
    have hp := p_monotone hx hxy
    linarith only [hp]

theorem pc_shift_exp {x t : ℝ} (hx : 0≤x) (ht : 0≤t) : Pc (x+t)≤Pc x*Real.exp t := by
  have hp := p_shift_exp hx ht
  have he : 1≤Real.exp t := Real.one_le_exp ht
  have hc := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤9677/20)
  dsimp only [Pc]
  nlinarith only [hp,hc]

theorem fine_base_rational : (900/23:ℝ)^2*Rho*P (18538073/1000000)<112456000 := by
  norm_num [Rho,P]

theorem coarse_base_rational : (32:ℝ)^2*Rho*Pc (18538073/1000000)<112456000 := by
  norm_num [Rho,Pc,P]

theorem exp_profile_gate {f : ℝ→ℝ} {C : ℝ} (hC : 0≤C)
    (hshift : ∀{x t:ℝ},0≤x→0≤t→f (x+t)≤f x*Real.exp t)
    (hbase : C*f (Real.log (112456000:ℝ))≤112456000) {n:ℝ} (hn:112456000≤n) :
    C*f (Real.log n)≤n := by
  have hn0 : 0<n := by linarith only [hn]
  have hlog : Real.log (112456000:ℝ)≤Real.log n := Real.log_le_log (by norm_num) hn
  have hp := hshift (Real.log_nonneg (by norm_num : (1:ℝ)≤112456000)) (sub_nonneg.mpr hlog)
  have he : Real.log (112456000:ℝ)+(Real.log n-Real.log (112456000:ℝ))=Real.log n := by ring
  have hex : Real.exp (Real.log n-Real.log (112456000:ℝ))=n/112456000 := by
    rw [Real.exp_sub,Real.exp_log hn0,Real.exp_log (by norm_num : (0:ℝ)<112456000)]
  rw [he,hex] at hp
  calc
    _≤C*(f (Real.log (112456000:ℝ))*(n/112456000)) := mul_le_mul_of_nonneg_left hp hC
    _=(C*f (Real.log (112456000:ℝ)))*(n/112456000) := by ring
    _≤112456000*(n/112456000) := mul_le_mul_of_nonneg_right hbase (by positivity)
    _=n := by ring

theorem fine_gate_real {n:ℝ} (hn:112456000≤n) : (900/23:ℝ)^2*Rho*P (Real.log n)≤n := by
  apply exp_profile_gate (by norm_num [Rho]) p_shift_exp ?_ hn
  have hp := mul_le_mul_of_nonneg_left
    (p_monotone (Real.log_nonneg (by norm_num : (1:ℝ)≤112456000)) log_base_upper.le)
    (by norm_num [Rho] : 0≤(900/23:ℝ)^2*Rho)
  linarith only [hp,fine_base_rational]

theorem coarse_gate_real {n:ℝ} (hn:112456000≤n) : (32:ℝ)^2*Rho*Pc (Real.log n)≤n := by
  apply exp_profile_gate (by norm_num [Rho]) pc_shift_exp ?_ hn
  have hp := mul_le_mul_of_nonneg_left
    (pc_monotone (Real.log_nonneg (by norm_num : (1:ℝ)≤112456000)) log_base_upper.le)
    (by norm_num [Rho] : 0≤(32:ℝ)^2*Rho)
  linarith only [hp,coarse_base_rational]

#print axioms log_base_upper
#print axioms p_nonnegative
#print axioms p_monotone
#print axioms p_shift_certificate
#print axioms p_shift_exp
#print axioms pc_monotone
#print axioms pc_shift_exp
#print axioms fine_base_rational
#print axioms coarse_base_rational
#print axioms exp_profile_gate
#print axioms fine_gate_real
#print axioms coarse_gate_real
end
end JSP233.DirectGate128
