module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace JSP233.SieveScalars88404
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem endpoint_cubic {a b y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hyb : y ≤ b) (hab : 12*a*b ≤ 1) :
    y^2-8*a*y^3 ≤ b^2-8*a*b^3 := by
  have hb : 0 ≤ b := hy.trans hyb
  have hd : 0 ≤ b-y := sub_nonneg.mpr hyb
  have hp := mul_nonneg (mul_nonneg hd (add_nonneg hb hy)) (sub_nonneg.mpr hab)
  have hq := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ha)
    (sq_nonneg (b-y))) (show 0 ≤ b+2*y by linarith only [hb, hy])
  have he : b^2-8*a*b^3-(y^2-8*a*y^3) =
      (b-y)*(b+y)*(1-12*a*b)+4*a*(b-y)^2*(b+2*y) := by ring
  linarith only [hp, hq, he]

theorem quadratic_error_bound {n : ℝ} (hn : 1000 ≤ n) :
    (606450017/1803601800 : ℝ)*n^2+(13565611/18036018 : ℝ)*n+
      (2403389/5010005 : ℝ) ≤ n^2/2 := by
  have hp := mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ n by linarith only [hn])
  nlinarith only [hn, hp]

#print axioms endpoint_cubic
#print axioms quadratic_error_bound
end
end JSP233.SieveScalars88404
