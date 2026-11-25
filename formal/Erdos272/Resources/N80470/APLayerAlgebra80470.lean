module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace JSP233.APLayerAlgebra80470
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def F (n k x : ℝ) : ℝ := n^2/x+k^2*x

theorem f_difference {n k x y : ℝ} (hx : x≠0) (hy : y≠0) :
    F n k x-F n k y=(y-x)*(n^2/(x*y)-k^2) := by
  unfold F
  field_simp [hx, hy]
  <;> ring

theorem f_antitone {n k x y : ℝ} (hn : 0≤n) (hk : 0≤k)
    (hx : 0<x) (hy : 0<y) (hxy : x≤y) (hkx : k*x≤n) (hky : k*y≤n) :
    F n k y≤F n k x := by
  have hp := mul_le_mul hkx hky (mul_nonneg hk hy.le) hn
  have hd : 0<x*y := mul_pos hx hy
  have hq : k^2≤n^2/(x*y) := (le_div_iff₀ hd).mpr (by nlinarith only [hp])
  have hmul := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hq)
  rw [←f_difference hx.ne' hy.ne'] at hmul
  exact sub_nonneg.mp hmul

theorem f_monotone {n k x y : ℝ} (hn : 0≤n) (hk : 0≤k)
    (hx : 0<x) (hy : 0<y) (hxy : x≤y) (hkx : n≤k*x) (hky : n≤k*y) :
    F n k x≤F n k y := by
  have hp := mul_le_mul hkx hky hn (mul_nonneg hk hx.le)
  have hd : 0<x*y := mul_pos hx hy
  have hq : n^2/(x*y)≤k^2 := (div_le_iff₀ hd).mpr (by nlinarith only [hp])
  have hmul := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy)
    (sub_nonpos.mpr hq)
  rw [←f_difference hx.ne' hy.ne'] at hmul
  exact sub_nonpos.mp hmul

theorem square_endpoint {n k l t : ℝ} (hk : 1≤k) (hn : k*(k+1)≤n)
    (hl : 0<l) (hlb : l≤n/(k+1)+1)
    (htlo : n/k≤t) (hthi : t≤n/k+1) :
    n/(k+1)-(3*k+1)≤F n k l-F n k t := by
  have hk0 : 0<k := by linarith only [hk]
  have hk1 : 0<k+1 := by linarith only [hk]
  have hn0 : 0<n := (mul_pos hk0 hk1).trans_le hn
  let b := n/(k+1)+1
  let u := n/k+1
  have hb : 0<b := by dsimp only [b]; positivity
  have hu : 0<u := by dsimp only [u]; positivity
  have ht : 0<t := (div_pos hn0 hk0).trans_le htlo
  have hkb : k*b≤n := by
    apply (mul_le_mul_iff_left₀ hk1).mp
    have he : (k*b)*(k+1)=k*n+k*(k+1) := by
      dsimp only [b]
      field_simp [hk1.ne']
      <;> ring
    rw [he]
    nlinarith only [hn]
  have hkl : k*l≤n := (mul_le_mul_of_nonneg_left hlb hk0.le).trans hkb
  have hleft := f_antitone hn0.le hk0.le hl hb hlb hkl hkb
  have hkt : n≤k*t := by
    have hh := (div_le_iff₀ hk0).mp htlo
    nlinarith only [hh]
  have hku : n≤k*u := by
    have he : k*u=n+k := by
      dsimp only [u]
      field_simp [hk0.ne']
      <;> ring
    rw [he]
    linarith only [hk0]
  have hright := f_monotone hn0.le hk0.le ht hu hthi hkt hku
  have hnplus : 0<n+k+1 := by positivity
  have hnplus0 : 0<n+k := by positivity
  have hbvalue : F n k b=n*(2*k+1/(k+1))-(2*k+1)+(k+1)^3/(n+k+1) := by
    dsimp only [F, b]
    field_simp [hk1.ne', hnplus.ne']
    <;> ring
  have huvalue : F n k u=2*n*k+k^3/(n+k) := by
    dsimp only [F, u]
    field_simp [hk0.ne', hnplus0.ne']
    <;> ring
  have hsmall : k^3/(n+k)≤k := by
    have hp := mul_le_mul_of_nonneg_left hn hk0.le
    apply (div_le_iff₀ hnplus0).mpr
    nlinarith only [hp, sq_nonneg k]
  have hpositive : 0≤(k+1)^3/(n+k+1) := by positivity
  rw [hbvalue] at hleft
  rw [huvalue] at hright
  simp only [div_eq_mul_inv] at hleft hright hsmall hpositive ⊢
  nlinarith only [hleft, hright, hsmall, hpositive]

theorem linear_endpoint {n k l r m : ℝ} (hk : 1≤k) (hn : k*(k+1)≤n)
    (hm : n/(k*(k+1))-1≤m) (hsum : l+r≤n/k+n/(k+1)+1) :
    n/(2*(k+1)^2)-1≤m*(k-k^2*(l+r)/(2*n)) := by
  have hk0 : 0<k := by linarith only [hk]
  have hk1 : 0<k+1 := by linarith only [hk]
  have hn0 : 0<n := (mul_pos hk0 hk1).trans_le hn
  let a := n/(k*(k+1))-1
  let b := k/(2*(k+1))-k^2/(2*n)
  have ha : 0≤a := by
    dsimp only [a]
    apply sub_nonneg.mpr
    exact (le_div_iff₀ (mul_pos hk0 hk1)).mpr (by nlinarith only [hn])
  have hb : 0≤b := by
    dsimp only [b]
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by positivity : 0<2*n) (by positivity : 0<2*(k+1))).mpr
    have hp := mul_le_mul_of_nonneg_left hn hk0.le
    nlinarith only [hp]
  have hm0 : 0≤m := ha.trans hm
  have hbracket : b≤k-k^2*(l+r)/(2*n) := by
    have hpaid := mul_le_mul_of_nonneg_left hsum (show 0≤k^2/(2*n) by positivity)
    have he : k-k^2*(n/k+n/(k+1)+1)/(2*n)=b := by
      dsimp only [b]
      field_simp [hk0.ne', hk1.ne', hn0.ne']
      <;> ring
    rw [←he]
    simp only [div_eq_mul_inv] at hpaid ⊢
    nlinarith only [hpaid]
  have hp := mul_le_mul hm hbracket hb hm0
  have he : a*b=n/(2*(k+1)^2)-k/(k+1)+k^2/(2*n) := by
    dsimp only [a, b]
    field_simp [hk0.ne', hk1.ne', hn0.ne']
    <;> ring
  have hkfrac : k/(k+1)≤1 := (div_le_iff₀ hk1).mpr (by linarith)
  have hpos : 0≤k^2/(2*n) := by positivity
  rw [he] at hp
  nlinarith only [hp, hkfrac, hpos]

theorem linear_tangent {n k d : ℝ} (hn : 0<n) (hd : 0<d) :
    k-k^2*d/n≤n/d-k := by
  have he : (n/d-k)-(k-k^2*d/n)=(n-k*d)^2/(n*d) := by
    field_simp [hn.ne', hd.ne']
    <;> ring
  have hp : 0≤(n-k*d)^2/(n*d) := by positivity
  rw [←he] at hp
  exact sub_nonneg.mp hp

theorem reciprocal_square_lower {d : ℝ} (hd : 0<d) :
    1/(d*(d+1))≤1/d^2 := by
  apply (div_le_div_iff₀ (by positivity : 0<d*(d+1)) (sq_pos_of_pos hd)).mpr
  nlinarith only [hd]

theorem half_integer_upper {d : ℝ} (hd : 1≤d) :
    1/d^2≤2/(2*d-1)-2/(2*d+1) := by
  have hd0 : 0<d := by linarith only [hd]
  have hm : 0<2*d-1 := by linarith only [hd]
  have hp : 0<2*d+1 := by positivity
  have he : 2/(2*d-1)-2/(2*d+1)=4/((2*d-1)*(2*d+1)) := by
    field_simp [hm.ne', hp.ne']
    <;> ring
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd0) (mul_pos hm hp)).mpr
  nlinarith

#print axioms f_difference
#print axioms f_antitone
#print axioms f_monotone
#print axioms square_endpoint
#print axioms linear_endpoint
#print axioms linear_tangent
#print axioms reciprocal_square_lower
#print axioms half_integer_upper
end
end JSP233.APLayerAlgebra80470
