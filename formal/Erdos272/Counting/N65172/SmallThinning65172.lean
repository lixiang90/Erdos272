module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace JSP233.SmallThinning65172
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem thin_payment {N t : ℕ} (hN : 48≤N) (hhi : N≤65967)
    (hthin : t≤N*(N-1)/5852) : (t : ℝ)≤78*(N : ℝ)-3159 := by
  have hprod : t*5852≤N*(N-1) :=
    (Nat.le_div_iff_mul_le (by norm_num : 0<5852)).mp hthin
  have hfactor : N-1≤12*5852 :=
    (Nat.sub_le N 1).trans (hhi.trans (by norm_num))
  have hmul := Nat.mul_le_mul_left N hfactor
  have hlinear : t≤12*N := by nlinarith only [hprod,hmul]
  have hreal : (t : ℝ)≤((12*N : ℕ) : ℝ) := Nat.cast_le.mpr hlinear
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hreal
  have hstart : ((48 : ℕ) : ℝ)≤(N : ℝ) := Nat.cast_le.mpr hN
  simp only [Nat.cast_ofNat] at hstart
  linarith only [hreal,hstart]

#print axioms thin_payment
end JSP233.SmallThinning65172
