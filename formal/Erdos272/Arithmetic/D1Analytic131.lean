module

public import Erdos272.Arithmetic.Hyperbola131
public import Erdos272.Arithmetic.HarmonicWindow131
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Floor.Semifield

@[expose] public section
namespace JSP233.D1Analytic131
open Hyperbola131 HarmonicWindow131 SimplexMoment57 HarmonicAbel29
open Set MeasureTheory intervalIntegral
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem log_trap_upper {r:ℝ} (hr:1≤r) : 2*r*Real.log r≤r^2-1 := by
  have hr0 : 0<r := lt_of_lt_of_le zero_lt_one hr
  have hc : ContinuousOn (fun t:ℝ=>1/t) (Icc 1 r) := by
    intro t ht
    exact (continuousAt_const.div continuousAt_id (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).continuousWithinAt
  have hv := (ConvexQuotient130.quotient_convex (x:=1) (by norm_num)).subset
    (show Icc (1:ℝ) r⊆Ioi 0 from fun t ht=>lt_of_lt_of_le zero_lt_one ht.1) (convex_Icc _ _)
  have h := Trapezoid130.integral_trapezoid hr hc hv
  rw [integral_one_div_of_pos zero_lt_one hr0] at h
  norm_num only [div_one,one_div_one] at h
  have hp := mul_le_mul_of_nonneg_left h (show 0≤2*r by positivity)
  have he : 2*r*((r-1)*(1+1/r)/2)=r^2-1 := by field_simp;ring
  rw [he] at hp
  exact hp

theorem hyperbola_floor_window {x:ℝ} {m:ℕ} (hx:0≤x)
    (hlo:(m:ℝ)^2≤x) (hhi:x<((m:ℝ)+1)^2) :
    (DivCount 1 (Nat.floor x):ℝ)=
      2*(∑a∈Finset.Icc 1 m,(Nat.floor (x/(a:ℝ)):ℝ))-(m:ℝ)^2 := by
  have hml : m^2≤Nat.floor x := (Nat.le_floor_iff hx).mpr (by exact_mod_cast hlo)
  have hmh : Nat.floor x<(m+1)^2 := (Nat.floor_lt hx).mpr (by exact_mod_cast hhi)
  simpa only [Nat.floor_div_natCast] using actual_hyperbola_real hml hmh

theorem hyperbola_floor_sandwich {x:ℝ} {m:ℕ} (hx:0≤x)
    (hlo:(m:ℝ)^2≤x) (hhi:x<((m:ℝ)+1)^2) :
    2*x*Harmonic m-2*(m:ℝ)-(m:ℝ)^2≤(DivCount 1 (Nat.floor x):ℝ) ∧
      (DivCount 1 (Nat.floor x):ℝ)≤2*x*Harmonic m-(m:ℝ)^2 := by
  have he : (∑a∈Finset.Icc 1 m,x/(a:ℝ))=x*Harmonic m := by
    dsimp only [Harmonic]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  have hu : (∑a∈Finset.Icc 1 m,(Nat.floor (x/(a:ℝ)):ℝ))≤∑a∈Finset.Icc 1 m,x/(a:ℝ) := by
    apply Finset.sum_le_sum
    intro a _ha
    exact Nat.floor_le (div_nonneg hx (Nat.cast_nonneg a))
  have hl : (∑a∈Finset.Icc 1 m,(x/(a:ℝ)-1))≤∑a∈Finset.Icc 1 m,(Nat.floor (x/(a:ℝ)):ℝ) := by
    apply Finset.sum_le_sum
    intro a _ha
    have h := Nat.lt_floor_add_one (x/(a:ℝ))
    linarith only [h]
  rw [Finset.sum_sub_distrib,he] at hl
  rw [he] at hu
  simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one] at hl
  rw [hyperbola_floor_window hx hlo hhi]
  constructor <;> linarith only [hl,hu]

theorem lower_window {x m H D:ℝ} (hm:1≤m) (hx:0<x)
    (hlo:m^2≤x) (hhi:x<(m+1)^2)
    (hH:Real.log m+577/1000≤H) (hD:2*x*H-2*m-m^2≤D) :
    x*(Real.log x+3/20)-7*Real.sqrt x≤D := by
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
    D≤x*(Real.log x+4/25)+7*Real.sqrt x := by
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

theorem sqrt_floor_window {x:ℝ} (hx:1≤x) :
    1≤Nat.floor (Real.sqrt x) ∧
      ((Nat.floor (Real.sqrt x):ℕ):ℝ)^2≤x ∧
      x<(((Nat.floor (Real.sqrt x):ℕ):ℝ)+1)^2 := by
  have hx0 : 0≤x := by linarith only [hx]
  have hs1 : (1:ℝ)≤Real.sqrt x := (Real.le_sqrt (by norm_num) hx0).mpr (by simpa using hx)
  have hmS := Nat.floor_le (Real.sqrt_nonneg x)
  refine ⟨(Nat.one_le_floor_iff _).mpr hs1,?_,?_⟩
  · have h := (sq_le_sq₀ (Nat.cast_nonneg (Nat.floor (Real.sqrt x))) (Real.sqrt_nonneg x)).mpr hmS
    simpa only [Real.sq_sqrt hx0] using h
  · exact (Real.sqrt_lt hx0 (by positivity)).mp (Nat.lt_floor_add_one (Real.sqrt x))

theorem actual_d1_lower_large {x:ℝ} (hx:1≤x) :
    x*(Real.log x+3/20)-7*Real.sqrt x≤(DivCount 1 (Nat.floor x):ℝ) := by
  obtain ⟨hm,hlo,hhi⟩ := sqrt_floor_window hx
  have hs := hyperbola_floor_sandwich (by linarith only [hx] : 0≤x) hlo hhi
  exact lower_window (by exact_mod_cast hm) (by linarith only [hx]) hlo hhi (harmonic_lower hm) hs.1

theorem actual_d1_upper_large {x:ℝ} (hx:1≤x) :
    (DivCount 1 (Nat.floor x):ℝ)≤x*(Real.log x+4/25)+7*Real.sqrt x := by
  obtain ⟨hm,hlo,hhi⟩ := sqrt_floor_window hx
  have hs := hyperbola_floor_sandwich (by linarith only [hx] : 0≤x) hlo hhi
  exact upper_window (by exact_mod_cast hm) (by linarith only [hx]) hlo hhi (harmonic_upper hm) hs.2

theorem actual_d1_lower {x:ℝ} (hx:0≤x) :
    x*(Real.log x+3/20)-7*Real.sqrt x≤(DivCount 1 (Nat.floor x):ℝ) := by
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
    (DivCount 1 (Nat.floor x):ℝ)≤x*(Real.log x+4/25)+7*Real.sqrt x := by
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

#print axioms log_trap_upper
#print axioms hyperbola_floor_window
#print axioms hyperbola_floor_sandwich
#print axioms lower_window
#print axioms upper_window
#print axioms sqrt_floor_window
#print axioms actual_d1_lower_large
#print axioms actual_d1_upper_large
#print axioms actual_d1_lower
#print axioms actual_d1_upper
end
end JSP233.D1Analytic131
