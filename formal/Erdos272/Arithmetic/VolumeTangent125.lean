import Erdos272.Arithmetic.VolumeStep125

/-! An actual all-quotient tangent lower bound for the divisor third moment.
The full real-floor volume lower bound is proved by actual recursion in
VolumeStep125. Its tangent is taken at 2^24 with rational log2 windows;
the zero quotient is paid separately, without a supplied moment budget. -/
namespace JSP233.VolumeTangent125
open VolumeLower125 VolumeStep125 SimplexMoment57 HarmonicLog55
open Set
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Anchor : ℝ := (2:ℝ)^24

theorem v4_derivative {x : ℝ} (hx : 0<x) :
    HasDerivAt V4 ((Real.log x)^3/6) x := by
  have hl := Real.hasDerivAt_log hx.ne'
  have hp := (((((hl.pow 3).div_const 6).sub ((hl.pow 2).div_const 2)).add hl).sub_const 1)
  have hd := ((hasDerivAt_id x).mul hp).add_const 1
  convert hd using 1 <;> first | rfl | (simp only [Pi.add_apply,Pi.sub_apply,Pi.pow_apply,id_eq];field_simp [hx.ne'];ring)

theorem v4_slope_monotone : MonotoneOn (fun x:ℝ=>(Real.log x)^3/6) (Ici 1) := by
  intro x hx y _hy hxy
  have hl := Real.log_le_log (lt_of_lt_of_le zero_lt_one hx) hxy
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Real.log_nonneg hx) hl 3) (by norm_num)

theorem v4_tangent {x r : ℝ} (hx : 1≤x) (hr : 1≤r) :
    V4 r+(Real.log r)^3/6*(x-r)≤V4 x := by
  by_cases hrx : r≤x
  · have hc : ContinuousOn V4 (Icc r x) := by
      intro y hy
      exact (v4_derivative (lt_of_lt_of_le zero_lt_one (hr.trans hy.1))).continuousAt.continuousWithinAt
    have hd : DifferentiableOn ℝ V4 (interior (Icc r x)) := by
      intro y hy
      exact (v4_derivative (lt_of_lt_of_le zero_lt_one (hr.trans (interior_subset hy).1))).differentiableAt.differentiableWithinAt
    have hb : ∀y∈interior (Icc r x),(Real.log r)^3/6≤deriv V4 y := by
      intro y hy
      have hy' := interior_subset hy
      rw [(v4_derivative (lt_of_lt_of_le zero_lt_one (hr.trans hy'.1))).deriv]
      exact v4_slope_monotone hr (hr.trans hy'.1) hy'.1
    have h := (convex_Icc r x).mul_sub_le_image_sub_of_le_deriv hc hd hb
      r ⟨le_rfl,hrx⟩ x ⟨hrx,le_rfl⟩ hrx
    linarith only [h]
  · have hxr : x≤r := le_of_not_ge hrx
    have hc : ContinuousOn V4 (Icc x r) := by
      intro y hy
      exact (v4_derivative (lt_of_lt_of_le zero_lt_one (hx.trans hy.1))).continuousAt.continuousWithinAt
    have hd : DifferentiableOn ℝ V4 (interior (Icc x r)) := by
      intro y hy
      exact (v4_derivative (lt_of_lt_of_le zero_lt_one (hx.trans (interior_subset hy).1))).differentiableAt.differentiableWithinAt
    have hb : ∀y∈interior (Icc x r),deriv V4 y≤(Real.log r)^3/6 := by
      intro y hy
      have hy' := interior_subset hy
      rw [(v4_derivative (lt_of_lt_of_le zero_lt_one (hx.trans hy'.1))).deriv]
      exact v4_slope_monotone (hx.trans hy'.1) hr hy'.2
    have h := (convex_Icc x r).image_sub_le_mul_sub_of_deriv_le hc hd hb
      x ⟨le_rfl,hxr⟩ r ⟨hxr,le_rfl⟩ hxr
    linarith only [h]

theorem anchor_log : Real.log Anchor=24*Real.log 2 := by
  rw [Anchor,Real.log_pow]
  norm_num

theorem anchor_slope_lower : (95911/125:ℝ)≤(Real.log Anchor)^3/6 := by
  rw [anchor_log]
  have hp : (24*(149337754816/215448838605:ℝ))^3≤(24*Real.log 2)^3 := by
    gcongr
    exact actual_log_two_lower
  have hrat : (95911/125:ℝ)≤(24*(149337754816/215448838605:ℝ))^3/6 := by norm_num
  linarith only [hp,hrat]

theorem anchor_intercept_upper :
    Anchor*((Real.log Anchor)^2/2-Real.log Anchor+1)-1≤(2059156015:ℝ) := by
  have hl : 24*(149337754816/215448838605:ℝ)≤Real.log Anchor := by
    rw [anchor_log]
    exact mul_le_mul_of_nonneg_left actual_log_two_lower (by norm_num)
  have hu : Real.log Anchor≤24*(173287/250000:ℝ) := by
    rw [anchor_log]
    exact mul_le_mul_of_nonneg_left actual_log_two_upper (by norm_num)
  have h0 : 0≤Real.log Anchor := Real.log_nonneg (by norm_num [Anchor])
  have hs : (Real.log Anchor)^2≤(24*(173287/250000:ℝ))^2 := by
    nlinarith only [hu,h0]
  have hrat : Anchor*((24*(173287/250000:ℝ))^2/2-
      24*(149337754816/215448838605:ℝ)+1)-1≤(2059156015:ℝ) := by norm_num [Anchor]
  have hr : Anchor=(16777216:ℝ) := by norm_num [Anchor]
  rw [hr] at hl hs hrat ⊢
  linarith only [hl,hs,hrat]

theorem actual_v4_rational_tangent {x : ℝ} (hx : 1≤x) :
    (95911/125:ℝ)*x-2059156015≤V4 x := by
  have ht := v4_tangent hx (r:=Anchor) (by norm_num [Anchor])
  have he : V4 Anchor+(Real.log Anchor)^3/6*(x-Anchor)=
      (Real.log Anchor)^3/6*x-(Anchor*((Real.log Anchor)^2/2-Real.log Anchor+1)-1) := by
    dsimp only [V4]
    ring
  rw [he] at ht
  calc
    _≤(Real.log Anchor)^3/6*x-2059156015 :=
      sub_le_sub_right (mul_le_mul_of_nonneg_right anchor_slope_lower (by linarith only [hx])) _
    _≤(Real.log Anchor)^3/6*x-(Anchor*((Real.log Anchor)^2/2-Real.log Anchor+1)-1) :=
      sub_le_sub_left anchor_intercept_upper _
    _≤_ := ht

theorem actual_div_count3_tangent (q : ℕ) :
    (95911/125:ℝ)*q-2059156015≤(DivCount 3 q:ℝ) := by
  by_cases hq : q=0
  · norm_num [hq,DivCount]
  · have hx : (1:ℝ)≤q := by exact_mod_cast (show 1≤q by omega)
    have hv := actual_v4_lower (x:=(q:ℝ)) hx
    simp only [Nat.floor_natCast] at hv
    exact (actual_v4_rational_tangent hx).trans hv

#print axioms v4_derivative
#print axioms v4_slope_monotone
#print axioms v4_tangent
#print axioms anchor_log
#print axioms anchor_slope_lower
#print axioms anchor_intercept_upper
#print axioms actual_v4_rational_tangent
#print axioms actual_div_count3_tangent
end
end JSP233.VolumeTangent125
