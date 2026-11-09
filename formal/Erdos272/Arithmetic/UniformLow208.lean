module

public import Erdos272.Arithmetic.StepWeightShape208
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-! The low-density side is one explicit cubic, including the closed D=2 boundary. -/
namespace JSP233.UniformLow208
open UniformSourceCore208 StepWeightShape208
noncomputable section
set_option maxHeartbeats 0

def LowJ (y z : ℝ) : ℝ :=
  (1-Delta*UniformSourceCore208.Sigma)*y^3/6+Delta*y*z^2/2-Delta*z^3/3+
    Delta*y*z/2-Delta*z^2/2-11*y^2/80-2014*y/625

theorem Jstar_low {y z : ℝ} (hy : 0<y) (hz : 0≤z) (hzy : 2*z≤y) :
    Jstar y z=LowJ y z := by
  have hm : 0<y-z := by linarith only [hy,hzy]
  have hrat1 : 1≤y/(y-z) := (le_div_iff₀ hm).mpr (by linarith only [hz])
  have hrat2 : y/(y-z)≤2 := (div_le_iff₀ hm).mpr (by linarith only [hzy])
  have hD1 : 1≤Step y (y-z) := Nat.le_floor (by simpa only [Nat.cast_one] using hrat1)
  have hD2 : Step y (y-z)≤2 := Nat.floor_le_of_le hrat2
  have hb := step_bounds hy.le hm
  have hcases : Step y (y-z)=1 ∨ Step y (y-z)=2 := by omega
  rcases hcases with hD | hD
  · unfold Jstar I w
    rw [hD]
    norm_num [H2,LowJ]
    ring
  · rw [hD] at hb
    norm_num only [Nat.cast_ofNat] at hb
    have he : y=2*z := by linarith only [hb.1,hzy]
    unfold Jstar I w
    rw [hD,he]
    norm_num [H2,LowJ,Finset.sum_Icc_succ_top]
    ring

def Cubic (c3 c2 c1 c0 x : ℝ) : ℝ := c3*x^3+c2*x^2+c1*x+c0

theorem cubic_min {a b x q c3 c2 c1 c0 : ℝ} (ha : 0≤a) (hax : a≤x) (hxb : x≤b)
    (hc3 : c3≤0) (hc2 : c2≤0)
    (hqa : q≤Cubic c3 c2 c1 c0 a) (hqb : q≤Cubic c3 c2 c1 c0 b) :
    q≤Cubic c3 c2 c1 c0 x := by
  by_cases hab : a=b
  · have hx : x=a := by linarith only [hax,hxb,hab]
    simpa only [hx] using hqa
  have hab' : 0<b-a := sub_pos.mpr (lt_of_le_of_ne (hax.trans hxb) hab)
  have hco : 0≤-c2-c3*(a+b+x) := by
    have hh := mul_nonpos_of_nonpos_of_nonneg hc3 (by linarith only [ha,hax,hxb] : 0≤a+b+x)
    linarith only [hc2,hh]
  have hp := mul_nonneg (mul_nonneg (mul_nonneg hab'.le (by linarith only [hax] : 0≤x-a))
    (by linarith only [hxb] : 0≤b-x)) hco
  have hid : (b-a)*Cubic c3 c2 c1 c0 x-(b-x)*Cubic c3 c2 c1 c0 a-
      (x-a)*Cubic c3 c2 c1 c0 b=(b-a)*(x-a)*(b-x)*(-c2-c3*(a+b+x)) := by
    unfold Cubic
    ring
  have hpa := mul_nonneg (by linarith only [hxb] : 0≤b-x) (sub_nonneg.mpr hqa)
  have hpb := mul_nonneg (by linarith only [hax] : 0≤x-a) (sub_nonneg.mpr hqb)
  have hres : 0≤(b-a)*(Cubic c3 c2 c1 c0 x-q) := by nlinarith only [hp,hid,hpa,hpb]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hab').mp hres)

#print axioms Jstar_low
#print axioms cubic_min
end
end JSP233.UniformLow208
