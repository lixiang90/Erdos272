module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

namespace JSP233.SmallCreditScalars84364
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Coefficient (L : ℕ) : ℕ := (L-1)^2+L
def Credit (L : ℕ) : ℕ := (L-1)^2*(L+1)+L.choose 2+2*L

theorem cross_mono {N m a b : ℕ} (hN : 2*m+3≤N) (ha : a≤m) (hb : b≤m) :
    (a : ℝ)*b*((N : ℝ)-2-((a : ℝ)+b)/2)+(m : ℝ)^2*((m : ℝ)+2)
      ≤(m : ℝ)^2*N := by
  have hNR : 2*(m : ℝ)+3≤(N : ℝ) := by exact_mod_cast hN
  have haR : (a : ℝ)≤(m : ℝ) := by exact_mod_cast ha
  have hbR : (b : ℝ)≤(m : ℝ) := by exact_mod_cast hb
  have hca : 0≤2*(N : ℝ)-4-(m : ℝ)-a-b := by nlinarith only [hNR, haR, hbR, Nat.cast_nonneg (α := ℝ) m]
  have hcb : 0≤2*(N : ℝ)-4-2*(m : ℝ)-b := by nlinarith only [hNR, hbR, Nat.cast_nonneg (α := ℝ) m]
  have hpA := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) b) (sub_nonneg.mpr haR)) hca
  have hpB := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sub_nonneg.mpr hbR)) hcb
  nlinarith only [hpA, hpB]

theorem two_hit_relax {N m a : ℕ} {f : ℝ} (hN : 2*m+3≤N) (ha : a≤m+1)
    (h : 2*f+(a : ℝ)*m*((a : ℝ)+m+2)≤
      2*(a : ℝ)*m*N+2*(((a-1)^2/4 : ℕ) : ℝ)) :
    2*f+((m : ℝ)+1)*m*(2*(m : ℝ)+3)≤
      2*((m : ℝ)+1)*m*N+2*((m^2/4 : ℕ) : ℝ) := by
  have hNR : 2*(m : ℝ)+3≤(N : ℝ) := by exact_mod_cast hN
  have haR : (a : ℝ)≤(m : ℝ)+1 := by exact_mod_cast ha
  have hfloor : (a-1)^2/4≤m^2/4 :=
    Nat.div_le_div_right (Nat.pow_le_pow_left (by omega : a-1≤m) 2)
  have hfloorR : (((a-1)^2/4 : ℕ) : ℝ)≤((m^2/4 : ℕ) : ℝ) := by exact_mod_cast hfloor
  have hc : 0≤2*(N : ℝ)-(a : ℝ)-2*m-3 := by nlinarith only [hNR, haR, Nat.cast_nonneg (α := ℝ) m]
  have hp := mul_nonneg (mul_nonneg (sub_nonneg.mpr haR) (Nat.cast_nonneg (α := ℝ) m)) hc
  nlinarith only [h, hfloorR, hp]

theorem no_singleton_credit {N m : ℕ} {f : ℝ}
    (hN : m+2+m^2/4≤N)
    (h : 2*f+((m : ℝ)+1)*m*(2*(m : ℝ)+3)≤
      2*((m : ℝ)+1)*m*N+2*((m^2/4 : ℕ) : ℝ)) :
    f+(m : ℝ)^2*((m : ℝ)+2)+((m+1).choose 2 : ℝ)+2*((m : ℝ)+1)
      ≤((m : ℝ)^2+(m : ℝ)+1)*N := by
  have hNR : (m : ℝ)+2+((m^2/4 : ℕ) : ℝ)≤(N : ℝ) := by exact_mod_cast hN
  rw [Nat.cast_choose_two]
  push_cast
  nlinarith only [h, hNR]

theorem trivial_credit {N m : ℕ} (hN : 2*m+3≤N) :
    1+(m : ℝ)^2*((m : ℝ)+2)+((m+1).choose 2 : ℝ)+2*((m : ℝ)+1)
      ≤((m : ℝ)^2+(m : ℝ)+1)*N := by
  have hNR : 2*(m : ℝ)+3≤(N : ℝ) := by exact_mod_cast hN
  have hm := Nat.cast_nonneg (α := ℝ) m
  have hcoef : 0≤(m : ℝ)^2+(m : ℝ)+1 := by positivity
  have hp := mul_nonneg hcoef (sub_nonneg.mpr hNR)
  have hc := mul_nonneg (sq_nonneg (m : ℝ)) hm
  rw [Nat.cast_choose_two]
  push_cast
  nlinarith only [hm, sq_nonneg (m : ℝ), hp, hc]

theorem rank_credit {N L a : ℕ} {f : ℝ} (hL : 2≤L) (hN : 2*L+1≤N)
    (hgap : L+1+(L-1)^2/4≤N) (ha : a≤L)
    (h : 2*f+(a : ℝ)*((L-1 : ℕ) : ℝ)*((a : ℝ)+((L-1 : ℕ) : ℝ)+2)≤
      2*(a : ℝ)*((L-1 : ℕ) : ℝ)*N+2*(((a-1)^2/4 : ℕ) : ℝ)) :
    f≤(Coefficient L : ℝ)*N-Credit L := by
  let m := L-1
  have hmL : m+1=L := Nat.sub_add_cancel (by omega : 1≤L)
  have hN' : 2*m+3≤N := by omega
  have ha' : a≤m+1 := by omega
  have hrelax := two_hit_relax hN' ha' h
  have hgap' : m+2+m^2/4≤N := by dsimp only [m]; omega
  have hpay := no_singleton_credit hgap' hrelax
  rw [← hmL]
  unfold Coefficient Credit
  simp only [Nat.add_sub_cancel]
  push_cast at hpay ⊢
  nlinarith only [hpay]

theorem trivial_credit_L {N L : ℕ} (hL : 2≤L) (hN : 2*L+1≤N) :
    1≤(Coefficient L : ℝ)*N-Credit L := by
  let m := L-1
  have hmL : m+1=L := Nat.sub_add_cancel (by omega : 1≤L)
  have hN' : 2*m+3≤N := by omega
  have hpay := trivial_credit hN'
  rw [← hmL]
  unfold Coefficient Credit
  simp only [Nat.add_sub_cancel]
  push_cast at hpay ⊢
  nlinarith only [hpay]

#print axioms cross_mono
#print axioms two_hit_relax
#print axioms no_singleton_credit
#print axioms trivial_credit
#print axioms rank_credit
#print axioms trivial_credit_L
end JSP233.SmallCreditScalars84364
