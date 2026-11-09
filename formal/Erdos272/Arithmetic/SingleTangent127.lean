module

public import Erdos272.Arithmetic.LogAnchor127
public import Erdos272.Arithmetic.ExclusionTangent126
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
namespace JSP233.SingleTangent127
open ExclusionTangent126 VolumeLower125 DivisorMoment122 SimplexMoment57
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def Slope : ℝ := LogAnchor127.AnchorSlope
def Intercept : ℝ := LogAnchor127.AnchorIntercept
theorem anchor_slope_bound : Slope≤S LogAnchor127.Anchor := by
  simpa only [Slope,S,D,LogAnchor127.AnchorSlope,LogAnchor127.SlopeExpr,LogAnchor127.Qprime]
    using LogAnchor127.anchor_slope_lower

theorem anchor_intercept_bound : LogAnchor127.Anchor*S LogAnchor127.Anchor-H LogAnchor127.Anchor≤Intercept := by
  have he : LogAnchor127.InterceptExpr=LogAnchor127.Anchor*S LogAnchor127.Anchor-H LogAnchor127.Anchor := by
    dsimp only [LogAnchor127.InterceptExpr,LogAnchor127.Qprime,S,H,V4,Q3,D]
    ring
  have hb := LogAnchor127.anchor_intercept_upper
  rw [he] at hb
  simpa only [Intercept,LogAnchor127.AnchorIntercept] using hb

theorem actual_h_rational_tangent {x : ℝ} (hx : 36≤x) : Slope*x-Intercept≤H x := by
  have ht := h_tangent hx (r:=LogAnchor127.Anchor) (by norm_num [LogAnchor127.Anchor])
  have he : H LogAnchor127.Anchor+S LogAnchor127.Anchor*(x-LogAnchor127.Anchor)=
      S LogAnchor127.Anchor*x-(LogAnchor127.Anchor*S LogAnchor127.Anchor-H LogAnchor127.Anchor) := by ring
  rw [he] at ht
  calc
    _≤S LogAnchor127.Anchor*x-Intercept :=
      sub_le_sub_right (mul_le_mul_of_nonneg_right anchor_slope_bound (by linarith only [hx])) _
    _≤S LogAnchor127.Anchor*x-(LogAnchor127.Anchor*S LogAnchor127.Anchor-H LogAnchor127.Anchor) :=
      sub_le_sub_left anchor_intercept_bound _
    _≤_ := ht

theorem actual_divisor_second_moment_single_exclusion (N : ℕ) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+Slope*N-Intercept≤(DivCount 3 N:ℝ) := by
  by_cases hN : 36≤N
  · have hn : (36:ℝ)≤N := by exact_mod_cast hN
    have hm := actual_second_moment_H hN
    have ht := actual_h_rational_tangent hn
    linarith only [hm,ht]
  · have hn : (N:ℝ)≤36 := by exact_mod_cast (show N≤36 by omega)
    have ht : Slope*(N:ℝ)-Intercept≤0 := by
      dsimp only [Slope,Intercept,LogAnchor127.AnchorSlope,LogAnchor127.AnchorIntercept]
      linarith only [hn]
    have hm := ParityPool123.actual_divisor_second_moment_parity N
    have hp := Nat.cast_nonneg (α:=ℝ) (DivCount 3 (N/4))
    linarith only [hm,hp,ht]

#print axioms anchor_slope_bound
#print axioms anchor_intercept_bound
#print axioms actual_h_rational_tangent
#print axioms actual_divisor_second_moment_single_exclusion
end
end JSP233.SingleTangent127
