module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace JSP233.FixedSmallScalars82427
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Coefficient (a m : ℕ) : ℕ := (a+1)*m+1

def Credit (a m : ℕ) : ℕ :=
  3*a*m+m*a.choose 2+a*m.choose 2+(m+1).choose 2+2*(m+1)

theorem credit_double (a m : ℕ) :
    2*(Credit a m : ℝ) =
      (a : ℝ)*m*((a : ℝ)+m+4)+((m : ℝ)+1)*((m : ℝ)+4) := by
  simp only [Credit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_choose_two]
  push_cast
  ring

theorem cross_mono_one {N a b m : ℕ}
    (hN : 2*m+3≤N) (ha : a≤m) (hb : b≤m) :
    (a : ℝ)*b*((N : ℝ)-2-((a : ℝ)+b)/2)+
      (a : ℝ)*m*((a : ℝ)+m+4)/2≤(a : ℝ)*m*N := by
  have hNR : 2*(m : ℝ)+3≤(N : ℝ) := by exact_mod_cast hN
  have haR : (a : ℝ)≤(m : ℝ) := by exact_mod_cast ha
  have hbR : (b : ℝ)≤(m : ℝ) := by exact_mod_cast hb
  have hc : 0≤2*(N : ℝ)-4-(a : ℝ)-m-b := by
    nlinarith only [hNR, haR, hbR, Nat.cast_nonneg (α := ℝ) m]
  have hp := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg (α := ℝ) a) (sub_nonneg.mpr hbR)) hc
  nlinarith only [hp]

theorem singleton_credit {N a b m : ℕ} {f root avoid : ℝ}
    (hN : 2*m+3≤N) (ha : a≤m) (hb : b≤m)
    (hpart : f=root+avoid)
    (hroot : 2*root+((m : ℝ)+1)*((m : ℝ)+4)≤2*((m : ℝ)+1)*N)
    (havoid : 2*avoid+(a : ℝ)*b*((a : ℝ)+b+4)≤2*(a : ℝ)*b*N) :
    f≤(Coefficient a m : ℝ)*N-Credit a m := by
  have hm := cross_mono_one hN ha hb
  have hc := credit_double a m
  simp only [Coefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at *
  nlinarith only [hpart, hroot, havoid, hm, hc]

theorem rank_credit {N a m : ℕ} {f : ℝ}
    (hN : m+2+a^2/4≤N)
    (h : 2*f+((a : ℝ)+1)*m*((a : ℝ)+m+3)≤
      2*((a : ℝ)+1)*m*N+2*((a^2/4 : ℕ) : ℝ)) :
    f≤(Coefficient a m : ℝ)*N-Credit a m := by
  have hn : (m : ℝ)+2+((a^2/4 : ℕ) : ℝ)≤(N : ℝ) := by exact_mod_cast hN
  have hc := credit_double a m
  simp only [Coefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  nlinarith only [h, hn, hc]

theorem anchor_mono {N a A m : ℕ}
    (hN : 2*m+3≤N) (ha : a≤A) (hA : A≤m) :
    (Coefficient a m : ℝ)*N-Credit a m≤
      (Coefficient A m : ℝ)*N-Credit A m := by
  have hNR : 2*(m : ℝ)+3≤(N : ℝ) := by exact_mod_cast hN
  have haR : (a : ℝ)≤(A : ℝ) := by exact_mod_cast ha
  have hAR : (A : ℝ)≤(m : ℝ) := by exact_mod_cast hA
  have hn : 0≤2*(N : ℝ)-(A : ℝ)-a-m-4 := by
    nlinarith only [hNR, haR, hAR, Nat.cast_nonneg (α := ℝ) m]
  have hp := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sub_nonneg.mpr haR)) hn
  have hca := credit_double a m
  have hcA := credit_double A m
  simp only [Coefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  nlinarith only [hp, hca, hcA]

#print axioms credit_double
#print axioms cross_mono_one
#print axioms singleton_credit
#print axioms rank_credit
#print axioms anchor_mono
end JSP233.FixedSmallScalars82427
