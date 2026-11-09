module

public import Erdos272.Arithmetic.D1Analytic131
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace JSP233.D1Sharper131
open D1Analytic131 Hyperbola131 HarmonicWindow131 SimplexMoment57 HarmonicAbel29
open Set MeasureTheory intervalIntegral
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem lower_window {x m H D:ℝ} (hm:1≤m) (hx:0<x)
    (hlo:m^2≤x) (hhi:x<(m+1)^2)
    (hH:Real.log m+577/1000≤H) (hD:2*x*H-2*m-m^2≤D) :
    x*(Real.log x+77/500)-2*Real.sqrt x-9/2≤D := by
  have hm0 : 0<m := lt_of_lt_of_le zero_lt_one hm
  let r := x/m^2
  have hr : 1≤r := (one_le_div (sq_pos_of_pos hm0)).mpr hlo
  have hr0 : 0<r := lt_of_lt_of_le zero_lt_one hr
  have hid : Real.log r=Real.log x-2*Real.log m := by
    dsimp only [r]
    rw [Real.log_div hx.ne' (pow_ne_zero 2 hm0.ne'),Real.log_pow]
    norm_num
  have hp := mul_le_mul_of_nonneg_left (log_trap_upper hr) (show 0≤m^4 by positivity)
  have he1 : m^4*(2*r*Real.log r)=2*x*m^2*Real.log r := by
    dsimp only [r]
    field_simp
  have he2 : m^4*(r^2-1)=x^2-m^4 := by
    dsimp only [r]
    field_simp
  rw [he1,he2] at hp
  have hd0 : 0≤x-m^2 := sub_nonneg.mpr hlo
  have hd3 : x-m^2≤3*m := by nlinarith only [hhi,hm]
  have hsq : (x-m^2)^2≤(3*m)^2 := (sq_le_sq₀ hd0 (by positivity)).mpr hd3
  have hrem : -(9/2:ℝ)≤x-m^2-x*Real.log r := by
    have hh : 0≤m^2*(x-m^2-x*Real.log r+9/2) := by nlinarith only [hp,hsq]
    have hn := nonneg_of_mul_nonneg_right hh (sq_pos_of_pos hm0)
    linarith only [hn]
  have hh := mul_le_mul_of_nonneg_left hH (show 0≤2*x by positivity)
  have hidmul : x*Real.log r=x*Real.log x-2*x*Real.log m := by rw [hid];ring
  have hmS : m≤Real.sqrt x := Real.le_sqrt_of_sq_le hlo
  nlinarith only [hD,hh,hrem,hidmul,hm,hmS,Real.sqrt_nonneg x,hx.le]

theorem upper_window {x m H D:ℝ} (hm:1≤m) (hx:0<x)
    (_hlo:m^2≤x) (hhi:x<(m+1)^2)
    (hH:H≤Real.log m+578/1000+1/(2*m)) (hD:D≤2*x*H-m^2) :
    D≤x*(Real.log x+39/250)+2*Real.sqrt x := by
  have hm0 : 0<m := lt_of_lt_of_le zero_lt_one hm
  let r := x/m^2
  have hr0 : 0<r := div_pos hx (sq_pos_of_pos hm0)
  have hid : Real.log r=Real.log x-2*Real.log m := by
    dsimp only [r]
    rw [Real.log_div hx.ne' (pow_ne_zero 2 hm0.ne'),Real.log_pow]
    norm_num
  have hp := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hr0) hx.le
  have he : x*(1-r⁻¹)=x-m^2 := by dsimp only [r];field_simp
  rw [he] at hp
  have hh := mul_le_mul_of_nonneg_left hH (show 0≤2*x by positivity)
  have hidmul : x*Real.log r=x*Real.log x-2*x*Real.log m := by rw [hid];ring
  have hcorr : 2*x*(1/(2*m))=x/m := by ring
  have hsm : Real.sqrt x<m+1 := (Real.sqrt_lt hx.le (by positivity)).mpr hhi
  have hsm2 : Real.sqrt x≤2*m := by linarith only [hsm,hm]
  have hprod := mul_nonneg (Real.sqrt_nonneg x) (sub_nonneg.mpr hsm2)
  have hxdiv : x/m≤2*Real.sqrt x := (div_le_iff₀ hm0).mpr (by nlinarith only [hprod,Real.sq_sqrt hx.le])
  have hh2 : 2*x*H≤2*x*Real.log m+(1156/1000)*x+x/m := by
    calc
      _≤2*x*(Real.log m+578/1000+1/(2*m)) := hh
      _=_ := by rw [mul_add,mul_add,hcorr];ring
  nlinarith only [hD,hh2,hp,hidmul,hxdiv,Real.sqrt_nonneg x,hx.le]

theorem actual_d1_lower_large {x:ℝ} (hx:1≤x) :
    x*(Real.log x+77/500)-2*Real.sqrt x-9/2≤(DivCount 1 (Nat.floor x):ℝ) := by
  obtain ⟨hm,hlo,hhi⟩ := sqrt_floor_window hx
  have hs := hyperbola_floor_sandwich (by linarith only [hx] : 0≤x) hlo hhi
  exact lower_window (by exact_mod_cast hm) (by linarith only [hx]) hlo hhi (harmonic_lower hm) hs.1

theorem actual_d1_upper_large {x:ℝ} (hx:1≤x) :
    (DivCount 1 (Nat.floor x):ℝ)≤x*(Real.log x+39/250)+2*Real.sqrt x := by
  obtain ⟨hm,hlo,hhi⟩ := sqrt_floor_window hx
  have hs := hyperbola_floor_sandwich (by linarith only [hx] : 0≤x) hlo hhi
  exact upper_window (by exact_mod_cast hm) (by linarith only [hx]) hlo hhi (harmonic_upper hm) hs.2

theorem actual_d1_lower {x:ℝ} (hx:0≤x) :
    x*(Real.log x+77/500)-2*Real.sqrt x-9/2≤(DivCount 1 (Nat.floor x):ℝ) := by
  by_cases hlarge:1≤x
  · exact actual_d1_lower_large hlarge
  · have hsmall : x<1 := lt_of_not_ge hlarge
    rw [Nat.floor_eq_zero.mpr hsmall]
    simp only [DivCount,Finset.Icc_eq_empty_of_lt (by decide : (0:ℕ)<1),Finset.sum_empty,Nat.cast_zero]
    have hl := Real.log_nonpos hx hsmall.le
    have hp := mul_nonpos_of_nonneg_of_nonpos hx hl
    have hs : x≤Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith only [mul_nonneg hx (sub_nonneg.mpr hsmall.le)])
    nlinarith only [hp,hs,Real.sqrt_nonneg x]

theorem actual_d1_upper {x:ℝ} (hx:0≤x) :
    (DivCount 1 (Nat.floor x):ℝ)≤x*(Real.log x+39/250)+2*Real.sqrt x := by
  by_cases hlarge:1≤x
  · exact actual_d1_upper_large hlarge
  · have hsmall : x<1 := lt_of_not_ge hlarge
    rw [Nat.floor_eq_zero.mpr hsmall]
    simp only [DivCount,Finset.Icc_eq_empty_of_lt (by decide : (0:ℕ)<1),Finset.sum_empty,Nat.cast_zero]
    rcases eq_or_lt_of_le hx with rfl|hx0
    · norm_num
    · have hs0 : 0<Real.sqrt x := Real.sqrt_pos.mpr hx0
      have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hs0)
      rw [Real.log_inv,Real.log_sqrt hx] at hl
      have hp := mul_le_mul_of_nonneg_left hl hx
      have he : x*(Real.sqrt x)⁻¹=Real.sqrt x := by
        calc
          _=(Real.sqrt x)^2*(Real.sqrt x)⁻¹ := by rw [Real.sq_sqrt hx]
          _=Real.sqrt x := by rw [pow_two,mul_assoc,mul_inv_cancel₀ hs0.ne',mul_one]
      rw [mul_sub,he,mul_one] at hp
      nlinarith only [hp,hx,Real.sqrt_nonneg x]

#print axioms lower_window
#print axioms upper_window
#print axioms actual_d1_lower_large
#print axioms actual_d1_upper_large
#print axioms actual_d1_lower
#print axioms actual_d1_upper
end
end JSP233.D1Sharper131
