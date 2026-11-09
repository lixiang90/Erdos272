module

public import Erdos272.Arithmetic.LightPrice208
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! The phase majorant used by the divisor-defect light price. -/
namespace JSP233.LightPhaseAnalytic209
open scoped BigOperators
open MeasureTheory Set intervalIntegral
noncomputable section
set_option maxHeartbeats 0

def Cap (N V E x : ℝ) : ℝ := min (V*x) (N+E*x)

def Coeff (V E k : ℝ) : ℝ :=
  V/(2*k^2)-(max (V-E-k) 0)^2/(2*(V-E)*k^2)

theorem cap_nonneg {N V E x : ℝ} (hN : 0≤N) (hV : 0≤V)
    (hE : 0≤E) (hx : 0≤x) : 0≤Cap N V E x := by
  exact le_min (mul_nonneg hV hx) (add_nonneg hN (mul_nonneg hE hx))

theorem cap_mono {N V E : ℝ} (hV : 0≤V) (hE : 0≤E) : Monotone (Cap N V E) := by
  intro x y hxy
  exact min_le_min (mul_le_mul_of_nonneg_left hxy hV)
    (by linarith only [mul_le_mul_of_nonneg_left hxy hE])

theorem cap_continuous (N V E : ℝ) : Continuous (Cap N V E) := by
  unfold Cap
  fun_prop

theorem linear_integral (a b c e : ℝ) :
    (∫ x in a..b, c+e*x)=c*(b-a)+e*(b^2-a^2)/2 := by
  have hd : ∀x:ℝ, HasDerivAt (fun y => c*y+e/2*y^2) (c+e*x) x := by
    intro x
    convert ((hasDerivAt_id x).const_mul c).add
      (((hasDerivAt_id x).pow 2).const_mul (e/2)) using 1 <;> first | rfl | (dsimp; ring)
  have hi : IntervalIntegrable (fun x:ℝ => c+e*x) volume a b :=
    (show Continuous (fun x:ℝ => c+e*x) by fun_prop).intervalIntegrable a b
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
  ring

theorem cap_integral {N V E k : ℝ} (hN : 0≤N) (hE : 0≤E)
    (hEV : E<V) (hk : 0<k) :
    (∫ x in (0:ℝ)..N/k, Cap N V E x)=N^2*Coeff V E k := by
  have hC : 0<V-E := sub_pos.mpr hEV
  have hX : 0≤N/k := div_nonneg hN hk.le
  by_cases hlarge : V-E≤k
  · have he : (∫ x in (0:ℝ)..N/k, Cap N V E x)=
        ∫ x in (0:ℝ)..N/k, (0+V*x) := by
      apply integral_congr
      intro x hx
      rw [uIcc_of_le hX] at hx
      have hmul : (V-E)*x≤N := by
        have hx0 : 0≤x := hx.1
        have h1 := mul_le_mul_of_nonneg_right hlarge hx0
        have h2 := (le_div_iff₀ hk).mp hx.2
        nlinarith only [h1,h2]
      simp only [Cap, zero_add, min_eq_left (by linarith : V*x≤N+E*x)]
    rw [he,linear_integral]
    simp only [Coeff,max_eq_right (by linarith : V-E-k≤0),zero_pow (by decide : 2≠0),zero_div,sub_zero]
    field_simp [ne_of_gt hk, ne_of_gt hC]
    <;> ring
  · have hkC : k<V-E := lt_of_not_ge hlarge
    have hY : 0≤N/(V-E) := div_nonneg hN hC.le
    have hYX : N/(V-E)≤N/k := div_le_div_of_nonneg_left hN hk hkC.le
    have hleft : (∫ x in (0:ℝ)..N/(V-E), Cap N V E x)=
        ∫ x in (0:ℝ)..N/(V-E), (0+V*x) := by
      apply integral_congr
      intro x hx
      rw [uIcc_of_le hY] at hx
      have hm := (le_div_iff₀ hC).mp hx.2
      simp only [Cap,zero_add,min_eq_left (by nlinarith only [hm] : V*x≤N+E*x)]
    have hright : (∫ x in N/(V-E)..N/k, Cap N V E x)=
        ∫ x in N/(V-E)..N/k, (N+E*x) := by
      apply integral_congr
      intro x hx
      rw [uIcc_of_le hYX] at hx
      have hm := (div_le_iff₀ hC).mp hx.1
      simp only [Cap,min_eq_right (by nlinarith only [hm] : N+E*x≤V*x)]
    have hi (a b : ℝ) : IntervalIntegrable (Cap N V E) volume a b :=
      (cap_continuous N V E).intervalIntegrable a b
    rw [←integral_add_adjacent_intervals (hi 0 (N/(V-E))) (hi (N/(V-E)) (N/k)),
      hleft,hright,linear_integral,linear_integral]
    unfold Coeff
    rw [max_eq_left (by linarith : 0≤V-E-k)]
    field_simp [ne_of_gt hk, ne_of_gt hC]
    <;> ring

theorem cap_sum_le {N V E k : ℝ} {q : ℕ} (hN : 0≤N) (hE : 0≤E)
    (hEV : E<V) (hk : 0<k) (hq : (q:ℝ)≤N/k) :
    (∑ d∈Finset.Icc 1 q, Cap N V E d)≤N^2*Coeff V E k+V*N/k := by
  have hV : 0≤V := hE.trans hEV.le
  have hm := cap_mono (N:=N) hV hE
  have hf : MonotoneOn (Cap N V E) (Icc (0:ℝ) q) := hm.monotoneOn _
  have hs : (∑d∈Finset.Ico 0 q,Cap N V E d)≤∫x in (0:ℝ)..q,Cap N V E x := by
    simpa only [zero_add,Finset.range_eq_Ico] using
      (MonotoneOn.sum_le_integral (a:=q) (x₀:=0) (f:=Cap N V E) (by simpa using hf))
  have hsum : (∑d∈Finset.Icc 1 q,Cap N V E d)=
      (∑d∈Finset.Ico 0 q,Cap N V E d)+Cap N V E q := by
    have hz : Cap N V E 0=0 := by simp [Cap,hN]
    have h1 := Finset.sum_eq_sum_Ico_succ_bot (f:=fun d:ℕ => Cap N V E d)
      (show 0<q+1 by omega)
    have h2 := Finset.sum_Ico_succ_top (f:=fun d:ℕ => Cap N V E d)
      (show 0≤q by omega)
    simp only [Nat.cast_zero,hz,zero_add] at h1
    rw [←Finset.Ico_add_one_right_eq_Icc]
    linarith only [h1,h2]
  have hi (a b : ℝ) : IntervalIntegrable (Cap N V E) volume a b :=
    (cap_continuous N V E).intervalIntegrable a b
  have hext : (∫x in (0:ℝ)..q,Cap N V E x)≤∫x in (0:ℝ)..N/k,Cap N V E x := by
    apply integral_mono_interval le_rfl (by exact_mod_cast Nat.zero_le q) hq ?_ (hi 0 (N/k))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact cap_nonneg hN hV hE hx.1.le
  have hp : Cap N V E q≤V*N/k := by
    have hh : Cap N V E q≤V*(q:ℝ) := min_le_left _ _
    have hh2 := mul_le_mul_of_nonneg_left hq hV
    simpa only [mul_div_assoc] using hh.trans hh2
  rw [cap_integral hN hE hEV hk] at hext
  rw [hsum]
  exact add_le_add (hs.trans hext) hp

theorem phase_le_cap {N d k r B V E : ℕ} (hd : 0<d) :
    (min d (N-k*d)*min V (N/d-r*B+E):ℕ) ≤ min (V*d) (N+E*d) := by
  apply le_min
  · simpa only [Nat.mul_comm] using
      Nat.mul_le_mul (min_le_left d (N-k*d)) (min_le_left V (N/d-r*B+E))
  · have hq : (N/d-r*B+E:ℕ)≤N/d+E :=
      Nat.add_le_add_right (Nat.sub_le (N/d) (r*B)) E
    have hmin := (min_le_right V (N/d-r*B+E)).trans hq
    have hprod := Nat.mul_le_mul (min_le_left d (N-k*d)) hmin
    have hdiv := Nat.div_mul_le_self N d
    nlinarith only [hprod,hdiv]

#print axioms cap_integral
#print axioms cap_sum_le
#print axioms phase_le_cap
end
end JSP233.LightPhaseAnalytic209
