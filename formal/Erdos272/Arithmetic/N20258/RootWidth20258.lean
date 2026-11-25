module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace JSP233.RootWidth20258

/-- With at most eight times the ground size in omitted crooked members,
the global quadratic profile already yields both terminal width bounds. -/
theorem axes {n l w : ℝ} (lo : 18000 ≤ n) (hl : 0 ≤ l) (hw : 0 ≤ w)
    (profile : (114959/80000)*l^2-(329/200)*l*w+w^2/2 ≤ 21*n+60*l+9*w+872) :
    l < n/6 ∧ w < n/4 := by
  have n0 : 0 ≤ n := by linarith only [lo]
  have nn := mul_le_mul_of_nonneg_right lo n0
  have left : l^2/6 ≤ 150*l+42*n+1825 := by
    nlinarith only [profile,sq_nonneg (w-(329/200)*l-9),sq_nonneg l,hl]
  have width : w^2/6 ≤ 250*w+121*n+8620 := by
    nlinarith only [profile,sq_nonneg (2*(114959/80000)*l-(329/200)*w-60),
      sq_nonneg w,hw,n0]
  constructor
  · by_contra! h
    have hmul := mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ (l+n/6)/6-150 by linarith only [h,lo])
    nlinarith only [hmul,left,lo,nn]
  · by_contra! h
    have hmul := mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ (w+n/4)/6-250 by linarith only [h,lo])
    nlinarith only [hmul,width,lo,nn]

#print axioms axes

theorem coarse_left {n l w : ℝ} (lo : 19227 ≤ n) (hl : 0 ≤ l)
    (profile : (114959/80000)*l^2-(329/200)*l*w+w^2/2 ≤ 25*n+74*l+12*w+872) :
    l < n/6 := by
  have bound : l^2/6 ≤ 188*l+50*n+1888 := by
    nlinarith only [profile,sq_nonneg (w-(329/200)*l-12),sq_nonneg l,hl]
  by_contra! h
  have mono := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ (l+n/6)/6-188 by linarith only [h,lo])
  have nn := mul_le_mul_of_nonneg_right lo (show 0 ≤ n by linarith only [lo])
  nlinarith only [mono,bound,lo,nn]

theorem fine_width {n l w : ℝ} (lo : 20000 ≤ n) (hw : 0 ≤ w)
    (profile : (114959/80000)*l^2-(329/200)*l*w+w^2/2 ≤ (241/10)*n+60*l+12*w+872) :
    w < n/4 := by
  have n0 : 0 ≤ n := by linarith only [lo]
  have bound : w^2/6 ≤ 267*w+139*n+8620 := by
    nlinarith only [profile,sq_nonneg (2*(114959/80000)*l-(329/200)*w-60),sq_nonneg w,hw,n0]
  by_contra! h
  have mono := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ (w+n/4)/6-267 by linarith only [h,lo])
  have nn := mul_le_mul_of_nonneg_right lo n0
  nlinarith only [mono,bound,lo,nn]

/-- A sharper width bound on the initial window, using the harmonic cap
from the fifteenth dyadic endpoint. -/
theorem fine_width_early {n l w : ℝ} (lo : 19227 ≤ n) (hw : 0 ≤ w)
    (profile : (114959/80000)*l^2-(329/200)*l*w+w^2/2 ≤
      (584/25)*n+59*l+(1103/100)*w+872) :
    w < n/4 := by
  have n0 : 0 ≤ n := by linarith only [lo]
  have bound : w^2/6 ≤ 256*w+134*n+8430 := by
    nlinarith only [profile,sq_nonneg (2*(114959/80000)*l-(329/200)*w-59),
      sq_nonneg w,hw,n0]
  by_contra! h
  have mono := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ (w+n/4)/6-256 by linarith only [h,lo])
  have nn := mul_le_mul_of_nonneg_right lo n0
  nlinarith only [mono,bound,lo,nn]

#print axioms coarse_left
#print axioms fine_width
end JSP233.RootWidth20258
