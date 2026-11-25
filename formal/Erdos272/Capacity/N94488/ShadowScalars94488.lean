module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace JSP233.ShadowScalars94488
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem low_cubic {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r^2/4-7*r^3/48 ≤ 5/48 := by
  have hp := mul_nonneg (sub_nonneg.mpr hr1) (show 0 ≤ 1+r by positivity)
  have hq := mul_nonneg (sq_nonneg (1-r)) (show 0 ≤ 1+2*r by positivity)
  nlinarith only [hp, hq]

theorem high_cubic {r : ℝ} (hr : r ≤ 3/2) :
    r^3/48-r^2/4+r/2-1/6 ≤ 219/2000 := by
  have hp := mul_nonneg (sq_nonneg (r-7/6)) (show 0 ≤ 3/2-r by linarith only [hr])
  have hq := sq_nonneg (r-7/6-1/196)
  nlinarith only [hp, hq]

theorem unit_low_scaled {H w g : ℝ} (hH : 0 < H) (hw : 0 ≤ w)
    (hwH : w ≤ H) (hgH : 6*g*H = 1) :
    w^2/4-7*g*w^3/8 ≤ (219/2000)*H^2 := by
  have hg : g = 1/(6*H) := by
    apply (eq_div_iff (show 6*H ≠ 0 by positivity)).mpr
    nlinarith only [hgH]
  have hr0 : 0 ≤ w/H := div_nonneg hw hH.le
  have hr1 : w/H ≤ 1 := (div_le_one hH).mpr hwH
  have hp := mul_le_mul_of_nonneg_left (low_cubic hr0 hr1) (sq_nonneg H)
  have he : H^2*((w/H)^2/4-7*(w/H)^3/48) = w^2/4-7*g*w^3/8 := by
    rw [hg]
    field_simp [hH.ne']
    <;> ring
  rw [he] at hp
  nlinarith only [hp, sq_nonneg H]

theorem unit_high_scaled {H w g : ℝ} (hH : 0 < H)
    (hwH : w ≤ 3*H/2) (hgH : 6*g*H = 1) :
    w^2/4-7*g*w^3/8+g*(w-H)^3 ≤ (219/2000)*H^2 := by
  have hg : g = 1/(6*H) := by
    apply (eq_div_iff (show 6*H ≠ 0 by positivity)).mpr
    nlinarith only [hgH]
  have hr : w/H ≤ 3/2 := (div_le_iff₀ hH).mpr (by linarith only [hwH])
  have hp := mul_le_mul_of_nonneg_left (high_cubic hr) (sq_nonneg H)
  have he : H^2*((w/H)^3/48-(w/H)^2/4+(w/H)/2-1/6) =
      w^2/4-7*g*w^3/8+g*(w-H)^3 := by
    rw [hg]
    field_simp [hH.ne']
    <;> ring
  rw [he] at hp
  simpa only [mul_comm] using hp

theorem unit_scalar {H w g K p s : ℝ} (hH : 0 < H) (hg : 0 < g)
    (hgH : 6*g*H = 1) (hw : 0 ≤ w) (hwH : w ≤ 3*H/2)
    (hKp : K ≤ p) (hpw : p ≤ w^2/4)
    (hmoment : ∀ x : ℝ, 0 ≤ x → w^3-6*(p-K)*(w-x)-x^3 ≤ 6*s+w) :
    K-g*(6*s+w-w^3/8) ≤ (219/2000)*H^2 := by
  by_cases hlow : w ≤ H
  · have hm := hmoment 0 le_rfl
    have hgw : 0 ≤ 1-6*g*w := by
      have hh := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 6*g by positivity)
      nlinarith only [hh, hgH]
    have hp := mul_nonneg (sub_nonneg.mpr hKp) hgw
    have hmg := mul_le_mul_of_nonneg_left hm hg.le
    have hc := unit_low_scaled hH hw hlow hgH
    nlinarith only [hp, hpw, hmg, hc]
  · have hm := hmoment (w-H) (by linarith only [hlow])
    have hmg := mul_le_mul_of_nonneg_left hm hg.le
    have hKg : 6*g*H*K = K := by rw [hgH]; ring
    have hpg : 6*g*H*p = p := by rw [hgH]; ring
    have hc := unit_high_scaled hH hwH hgH
    nlinarith only [hmg, hKg, hpg, hpw, hc]

theorem step_two_scalar {n y g : ℝ} (hn : 0 ≤ n) (hy : 0 ≤ y)
    (hyn : 4*y ≤ n) (hg : 0 ≤ g) (hcap : 4*g*n ≤ 1) :
    y^2-8*g*y^3 ≤ n^2/16-g*n^3/8 := by
  let b := n/4
  have hby : 0 ≤ b-y := by dsimp only [b]; linarith only [hyn]
  have hbr : 0 ≤ b+y := by dsimp only [b]; positivity
  have hcut : 0 ≤ 1-12*g*b := by dsimp only [b]; nlinarith only [hcap]
  have hp := mul_nonneg (mul_nonneg hby hbr) hcut
  have hq := mul_nonneg (mul_nonneg (show 0 ≤ 4*g by positivity) (sq_nonneg (b-y)))
    (show 0 ≤ b+2*y by dsimp only [b]; positivity)
  dsimp only [b] at hp hq
  nlinarith only [hp, hq]

#print axioms low_cubic
#print axioms high_cubic
#print axioms unit_low_scaled
#print axioms unit_high_scaled
#print axioms unit_scalar
#print axioms step_two_scalar
end
end JSP233.ShadowScalars94488
