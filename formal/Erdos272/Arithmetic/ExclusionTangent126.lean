module

public import Erdos272.Arithmetic.CompletePool126
public import Erdos272.Arithmetic.VolumeTangent125
public import Erdos272.Arithmetic.DivisorMoment122
public import Erdos272.Arithmetic.LogThree126
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace JSP233.ExclusionTangent126
open SimplexMoment57 DivisorMoment45 DivisorMoment122 VolumeLower125 VolumeTangent125
open scoped Classical BigOperators
open Set
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Slope : ℝ := 234101/1000
def Intercept : ℝ := 2174919308
def D (L : ℝ) : ℝ := L^2/2+(91/50)*L+18181/10000
def H (x : ℝ) : ℝ := V4 (x/4)+V4 (x/9)-(x/36)*Q3 (Real.log (x/36))
def S (x : ℝ) : ℝ := (Real.log (x/4))^3/24+(Real.log (x/9))^3/54-
  (Q3 (Real.log (x/36))+D (Real.log (x/36)))/36

theorem log_div_derivative {x d : ℝ} (hx : 0<x) (hd : 0<d) :
    HasDerivAt (fun y:ℝ=>Real.log (y/d)) x⁻¹ x := by
  have h := (Real.hasDerivAt_log (div_ne_zero hx.ne' hd.ne')).comp x ((hasDerivAt_id x).div_const d)
  convert h using 1 <;> first | rfl | field_simp

theorem q3_derivative (x : ℝ) : HasDerivAt Q3 (D x) x := by
  have h := (((((hasDerivAt_id x).pow 3).div_const 6).add
    ((((hasDerivAt_id x).pow 2).const_mul (91/100)))).add
    ((hasDerivAt_id x).const_mul (18181/10000))).add_const (2531/2000)
  convert h using 1 <;> first | rfl | (dsimp only [D,id_eq];ring)

theorem d_derivative (x : ℝ) : HasDerivAt D (x+91/50) x := by
  have h := ((((hasDerivAt_id x).pow 2).div_const 2).add
    ((hasDerivAt_id x).const_mul (91/50))).add_const (18181/10000)
  convert h using 1 <;> first | rfl | (dsimp only [id_eq];ring)

theorem h_derivative {x : ℝ} (hx : 0<x) : HasDerivAt H (S x) x := by
  have h4 := (v4_derivative (div_pos hx (by norm_num : (0:ℝ)<4))).comp x ((hasDerivAt_id x).div_const 4)
  have h9 := (v4_derivative (div_pos hx (by norm_num : (0:ℝ)<9))).comp x ((hasDerivAt_id x).div_const 9)
  have hq := (q3_derivative (Real.log (x/36))).comp x (log_div_derivative hx (by norm_num : (0:ℝ)<36))
  have hd := (h4.add h9).sub (((hasDerivAt_id x).div_const 36).mul hq)
  convert hd using 1 <;> first | rfl | (dsimp only [S,Function.comp_apply,id_eq];field_simp [hx.ne'];ring)

theorem s_derivative {x : ℝ} (hx : 0<x) : HasDerivAt S
    (((Real.log (x/4))^2/8+(Real.log (x/9))^2/18-
      ((Real.log (x/36))^2/2+(141/50)*Real.log (x/36)+36381/10000)/36)/x) x := by
  have h4 := ((log_div_derivative hx (by norm_num : (0:ℝ)<4)).pow 3).div_const 24
  have h9 := ((log_div_derivative hx (by norm_num : (0:ℝ)<9)).pow 3).div_const 54
  have hq := ((q3_derivative (Real.log (x/36))).add (d_derivative (Real.log (x/36)))).comp x
    (log_div_derivative hx (by norm_num : (0:ℝ)<36))
  have hd := (h4.add h9).sub (hq.div_const 36)
  convert hd using 1 <;> first | rfl | (dsimp only [D];field_simp [hx.ne'];ring)

theorem curvature_nonnegative {x : ℝ} (hx : 36≤x) :
    0≤(Real.log (x/4))^2/8+(Real.log (x/9))^2/18-
      ((Real.log (x/36))^2/2+(141/50)*Real.log (x/36)+36381/10000)/36 := by
  have hx0 : 0<x := by linarith only [hx]
  have hz : 0≤Real.log (x/36) := Real.log_nonneg ((one_le_div (by norm_num : (0:ℝ)<36)).mpr hx)
  have hl4 : (1:ℝ)≤Real.log 4 := by
    have he : (4:ℝ)=(2:ℝ)^2 := by norm_num
    rw [he,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [HarmonicLog55.actual_log_two_lower]
  have hl9 : (1:ℝ)≤Real.log 9 := hl4.trans (Real.log_le_log (by norm_num) (by norm_num : (4:ℝ)≤9))
  have h4 : Real.log (x/36)+1≤Real.log (x/4) := by
    have he : x/4=(x/36)*9 := by ring
    rw [he,Real.log_mul (by positivity : x/36≠0) (by norm_num : (9:ℝ)≠0)]
    linarith only [hl9]
  have h9 : Real.log (x/36)+1≤Real.log (x/9) := by
    have he : x/9=(x/36)*4 := by ring
    rw [he,Real.log_mul (by positivity : x/36≠0) (by norm_num : (4:ℝ)≠0)]
    linarith only [hl4]
  have hs4 := pow_le_pow_left₀ (by linarith only [hz] : 0≤Real.log (x/36)+1) h4 2
  have hs9 := pow_le_pow_left₀ (by linarith only [hz] : 0≤Real.log (x/36)+1) h9 2
  nlinarith only [hs4,hs9,hz,sq_nonneg (Real.log (x/36))]

theorem h_slope_monotone : MonotoneOn S (Ici (36:ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 36)
  · intro x hx
    exact (s_derivative (lt_of_lt_of_le (by norm_num : (0:ℝ)<36) hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (s_derivative (lt_of_lt_of_le (by norm_num : (0:ℝ)<36) (interior_subset hx))).differentiableAt.differentiableWithinAt
  · intro x hx
    have hh := interior_subset hx
    rw [(s_derivative (lt_of_lt_of_le (by norm_num : (0:ℝ)<36) hh)).deriv]
    exact div_nonneg (curvature_nonnegative hh) ((by norm_num : (0:ℝ)≤36).trans hh)

theorem h_tangent {x r : ℝ} (hx : 36≤x) (hr : 36≤r) : H r+S r*(x-r)≤H x := by
  by_cases hrx : r≤x
  · have hc : ContinuousOn H (Icc r x) := by
      intro y hy
      exact (h_derivative (by linarith only [hr,hy.1])).continuousAt.continuousWithinAt
    have hd : DifferentiableOn ℝ H (interior (Icc r x)) := by
      intro y hy
      have h := interior_subset hy
      exact (h_derivative (by linarith only [hr,h.1])).differentiableAt.differentiableWithinAt
    have hb : ∀y∈interior (Icc r x),S r≤deriv H y := by
      intro y hy
      have hy' := interior_subset hy
      rw [(h_derivative (by linarith only [hr,hy'.1])).deriv]
      exact h_slope_monotone hr (hr.trans hy'.1) hy'.1
    have h := (convex_Icc r x).mul_sub_le_image_sub_of_le_deriv hc hd hb r ⟨le_rfl,hrx⟩ x ⟨hrx,le_rfl⟩ hrx
    linarith only [h]
  · have hxr : x≤r := le_of_not_ge hrx
    have hc : ContinuousOn H (Icc x r) := by
      intro y hy
      exact (h_derivative (by linarith only [hx,hy.1])).continuousAt.continuousWithinAt
    have hd : DifferentiableOn ℝ H (interior (Icc x r)) := by
      intro y hy
      have h := interior_subset hy
      exact (h_derivative (by linarith only [hx,h.1])).differentiableAt.differentiableWithinAt
    have hb : ∀y∈interior (Icc x r),deriv H y≤S r := by
      intro y hy
      have hy' := interior_subset hy
      rw [(h_derivative (by linarith only [hx,hy'.1])).deriv]
      exact h_slope_monotone (hx.trans hy'.1) hr hy'.2
    have h := (convex_Icc x r).image_sub_le_mul_sub_of_deriv_le hc hd hb x ⟨le_rfl,hxr⟩ r ⟨hxr,le_rfl⟩ hxr
    linarith only [h]

theorem div_count3_real_upper {x : ℝ} (hx : 1≤x) :
    (DivCount 3 (Nat.floor x):ℝ)≤x*Q3 (Real.log x) := by
  have hq : 1≤Nat.floor x := (Nat.one_le_floor_iff x).mpr hx
  have hqr : (1:ℝ)≤Nat.floor x := by exact_mod_cast hq
  have hcast : (Nat.floor x:ℝ)≤x := Nat.floor_le (by linarith only [hx])
  have hlog := Real.log_le_log (lt_of_lt_of_le zero_lt_one hqr) hcast
  exact (div_count_three_prefix hq).trans (mul_le_mul hcast
    (q3_monotone (Real.log_nonneg hqr) hlog)
    (q3_nonnegative (Real.log_nonneg hqr)) (by linarith only [hx]))

theorem actual_second_moment_H {N : ℕ} (hN : 36≤N) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+H N≤(DivCount 3 N:ℝ) := by
  have hn : (36:ℝ)≤N := by exact_mod_cast hN
  have h4 : (1:ℝ)≤(N:ℝ)/4 := by linarith only [hn]
  have h9 : (1:ℝ)≤(N:ℝ)/9 := by linarith only [hn]
  have h36 : (1:ℝ)≤(N:ℝ)/36 := by linarith only [hn]
  have hv4 := VolumeStep125.actual_v4_lower h4
  have hv9 := VolumeStep125.actual_v4_lower h9
  have hu36 := div_count3_real_upper h36
  simp only [Nat.floor_div_ofNat,Nat.floor_natCast] at hv4 hv9 hu36
  have hm := CompletePool126.actual_divisor_second_moment_full_two_three N
  dsimp only [H]
  linarith only [hv4,hv9,hu36,hm]

theorem anchor_slope_bound : Slope≤S LogThree126.Anchor := by
  simpa only [Slope,S,D,LogThree126.AnchorSlope,LogThree126.SlopeExpr,LogThree126.Qprime]
    using LogThree126.anchor_slope_lower

theorem anchor_intercept_bound : LogThree126.Anchor*S LogThree126.Anchor-H LogThree126.Anchor≤Intercept := by
  have he : LogThree126.InterceptExpr=LogThree126.Anchor*S LogThree126.Anchor-H LogThree126.Anchor := by
    dsimp only [LogThree126.InterceptExpr,LogThree126.Qprime,S,H,V4,Q3,D]
    ring
  have hb := LogThree126.anchor_intercept_upper
  rw [he] at hb
  simpa only [Intercept,LogThree126.AnchorIntercept] using hb

theorem actual_h_rational_tangent {x : ℝ} (hx : 36≤x) : Slope*x-Intercept≤H x := by
  have ht := h_tangent hx (r:=LogThree126.Anchor) (by norm_num [LogThree126.Anchor])
  have he : H LogThree126.Anchor+S LogThree126.Anchor*(x-LogThree126.Anchor)=
      S LogThree126.Anchor*x-(LogThree126.Anchor*S LogThree126.Anchor-H LogThree126.Anchor) := by ring
  rw [he] at ht
  calc
    _≤S LogThree126.Anchor*x-Intercept :=
      sub_le_sub_right (mul_le_mul_of_nonneg_right anchor_slope_bound (by linarith only [hx])) _
    _≤S LogThree126.Anchor*x-(LogThree126.Anchor*S LogThree126.Anchor-H LogThree126.Anchor) :=
      sub_le_sub_left anchor_intercept_bound _
    _≤_ := ht

theorem slope_nonnegative : (0:ℝ)≤Slope := by norm_num [Slope]

theorem intercept_nonnegative : (0:ℝ)≤Intercept := by norm_num [Intercept]

theorem actual_divisor_second_moment_exclusion (N : ℕ) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+Slope*N-Intercept≤(DivCount 3 N:ℝ) := by
  by_cases hN : 36≤N
  · have hn : (36:ℝ)≤N := by exact_mod_cast hN
    have hm := actual_second_moment_H hN
    have ht := actual_h_rational_tangent hn
    linarith only [hm,ht]
  · have hn : (N:ℝ)≤36 := by exact_mod_cast (show N≤36 by omega)
    have ht : Slope*(N:ℝ)-Intercept≤0 := by
      dsimp only [Slope,Intercept]
      linarith only [hn]
    have hm := ParityPool123.actual_divisor_second_moment_parity N
    have hp := Nat.cast_nonneg (α:=ℝ) (DivCount 3 (N/4))
    linarith only [hm,hp,ht]

#print axioms log_div_derivative
#print axioms q3_derivative
#print axioms d_derivative
#print axioms h_derivative
#print axioms s_derivative
#print axioms curvature_nonnegative
#print axioms h_slope_monotone
#print axioms h_tangent
#print axioms div_count3_real_upper
#print axioms actual_second_moment_H
#print axioms anchor_slope_bound
#print axioms anchor_intercept_bound
#print axioms actual_h_rational_tangent
#print axioms slope_nonnegative
#print axioms intercept_nonnegative
#print axioms actual_divisor_second_moment_exclusion
end
end JSP233.ExclusionTangent126
