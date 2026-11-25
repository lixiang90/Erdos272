module

public import Erdos272.Resources.N118533.CorrelatedSource118533
public import Erdos272.Core.N180000.AnalyticCore180000

@[expose] public section

namespace JSP233.DenseBonus118533
open StarArithmetic130000 CorrelatedSource118533 CoreUnionSource200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem divided_choose_quadratic {a k : ℕ} (hk : 0 < k) (ha : 2*k ≤ a) :
    ((a : ℝ)/(k : ℝ))^2/2-3*((a : ℝ)/(k : ℝ))/2+1 ≤ ((a/k).choose 2 : ℝ) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hdiv := Nat.mod_add_div a k
  have hmod := Nat.mod_lt a hk
  have hbound : a ≤ k*(a/k+1) := by nlinarith only [hdiv, hmod]
  have hboundR : (a : ℝ) ≤ (k : ℝ)*((a/k : ℕ)+1) := by exact_mod_cast hbound
  have hfloor : (a : ℝ)/(k : ℝ)-1 ≤ (a/k : ℕ) := by
    have hh : (a : ℝ)/(k : ℝ) ≤ (a/k : ℕ)+1 :=
      (div_le_iff₀ hkR).mpr (by simpa only [mul_comm] using hboundR)
    linarith only [hh]
  have haR : 2*(k : ℝ) ≤ a := by exact_mod_cast ha
  have hx : (2 : ℝ) ≤ (a : ℝ)/(k : ℝ) := (le_div_iff₀ hkR).mpr haR
  have hproduct := mul_nonneg (sub_nonneg.mpr hfloor)
    (show (0 : ℝ) ≤ (a/k : ℕ)+(a : ℝ)/(k : ℝ)-2 by
      linarith only [hfloor, hx])
  have hchoose : 2*((a/k).choose 2 : ℝ)+(a/k : ℕ) = (a/k : ℕ)*(a/k : ℕ) := by
    exact_mod_cast APInterval208.choose_two_twice (a/k)
  nlinarith only [hproduct, hchoose]

theorem bonus_quadratic {a : ℕ} (ha : 92 ≤ a) :
    (121/5000 : ℝ)*(a : ℝ)^2-3/4*a+8 ≤ (Bonus Primes a : ℝ) := by
  have hs := Finset.sum_le_sum (s := Primes) (fun q hq =>
    divided_choose_quadratic (by have := (primes_odd q hq).1.pos; omega)
      (show 2*(2*q) ≤ a by
        have hq23 : q ≤ 23 := by
          simp only [Primes, Finset.mem_insert, Finset.mem_singleton] at hq
          omega
        omega))
  have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  norm_num [Primes, Bonus] at hs ⊢
  nlinarith only [hs, haR, sq_nonneg (a : ℝ)]

theorem combined_quadratic {a : ℕ} (ha : 92 ≤ a) (hcap : a ≤ 2^18) :
    (1471/5000 : ℝ)*(a : ℝ)^2-6*a+8 ≤ (UnitBound a+Bonus Primes a : ℕ) := by
  have hu := AnalyticCore180000.unit_large hcap
  have hb := bonus_quadratic ha
  push_cast
  linarith only [hu, hb]

#print axioms divided_choose_quadratic
#print axioms bonus_quadratic
#print axioms combined_quadratic
end
end JSP233.DenseBonus118533
