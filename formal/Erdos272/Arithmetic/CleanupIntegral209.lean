module

public import Erdos272.Arithmetic.HarmonicLog55
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.CleanupIntegral209
open MeasureTheory Set intervalIntegral
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Cap (N U x : ℝ) : ℝ := N/max (N/U) x
def Area (r : ℝ) : ℝ := if r≤1 then r else 1+Real.log r
def Tangent (r : ℝ) (j : ℕ) : ℝ := j*(173287/250000 : ℝ)+r/(2 : ℝ)^j

theorem cap_continuous {N U : ℝ} (hN : 0<N) (hU : 0<U) : Continuous (Cap N U) := by
  unfold Cap
  apply continuous_const.div (continuous_const.max continuous_id)
  intro x
  exact ne_of_gt ((div_pos hN hU).trans_le (le_max_left _ _))

theorem cap_antitone {N U : ℝ} (hN : 0<N) (hU : 0<U) : Antitone (Cap N U) := by
  intro x y hxy
  exact div_le_div_of_nonneg_left hN.le
    ((div_pos hN hU).trans_le (le_max_left _ _)) (max_le_max_left _ hxy)

theorem cap_nonneg {N U : ℝ} (hN : 0<N) (hU : 0<U) (x : ℝ) : 0≤Cap N U x := by
  exact div_nonneg hN.le ((div_pos hN hU).trans_le (le_max_left _ _)).le

theorem cap_left {N U x : ℝ} (hN : 0<N) (hU : 0<U) (hx : x≤N/U) : Cap N U x=U := by
  rw [Cap,max_eq_left hx]
  field_simp

theorem cap_right {N U x : ℝ} (hx : N/U≤x) : Cap N U x=N/x := by
  rw [Cap,max_eq_right hx]

theorem cap_eq_min {N U x : ℝ} (hN : 0<N) (hU : 0<U) (hx : 0<x) : Cap N U x=min U (N/x) := by
  by_cases hc : x≤N/U
  · rw [cap_left hN hU hc,min_eq_left]
    apply (le_div_iff₀ hx).mpr
    have hh:=(le_div_iff₀ hU).mp hc
    nlinarith only [hh]
  · have hc' : N/U≤x := le_of_lt (lt_of_not_ge hc)
    rw [cap_right hc',min_eq_right]
    apply (div_le_iff₀ hx).mpr
    have hh:=(div_le_iff₀ hU).mp hc'
    nlinarith only [hh]

theorem cap_integral {N U A : ℝ} (hN : 0<N) (hU : 0<U) (hA : 0<A) :
    (∫x in (0 : ℝ)..N/A,Cap N U x)=N*Area (U/A) := by
  have hX : 0≤N/A := (div_pos hN hA).le
  have hY : 0<N/U := div_pos hN hU
  have hi (a b : ℝ) : IntervalIntegrable (Cap N U) volume a b :=
    (cap_continuous hN hU).intervalIntegrable a b
  by_cases hUA : U≤A
  · have hXY : N/A≤N/U := div_le_div_of_nonneg_left hN.le hU hUA
    have he : (∫x in (0 : ℝ)..N/A,Cap N U x)=∫_x in (0 : ℝ)..N/A,U := by
      apply integral_congr
      intro x hx
      rw [uIcc_of_le hX] at hx
      exact cap_left hN hU (hx.2.trans hXY)
    rw [he,intervalIntegral.integral_const]
    rw [Area,if_pos ((div_le_one hA).mpr hUA)]
    simp only [smul_eq_mul,sub_zero]
    ring
  · have hAU : A<U := lt_of_not_ge hUA
    have hYX : N/U≤N/A := div_le_div_of_nonneg_left hN.le hA hAU.le
    have hleft : (∫x in (0 : ℝ)..N/U,Cap N U x)=∫_x in (0 : ℝ)..N/U,U := by
      apply integral_congr
      intro x hx
      rw [uIcc_of_le hY.le] at hx
      exact cap_left hN hU hx.2
    have hright : (∫x in N/U..N/A,Cap N U x)=∫x in N/U..N/A,N*x⁻¹ := by
      apply integral_congr
      intro x hx
      rw [uIcc_of_le hYX] at hx
      simpa only [div_eq_mul_inv] using cap_right hx.1
    rw [←integral_add_adjacent_intervals (hi 0 (N/U)) (hi (N/U) (N/A)),hleft,hright,
      intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_inv_of_pos hY (div_pos hN hA)]
    have hratio : (N/A)/(N/U)=U/A := by field_simp
    rw [hratio,Area,if_neg (by exact not_le.mpr ((one_lt_div hA).mpr hAU))]
    simp only [smul_eq_mul,sub_zero]
    field_simp [hN.ne',hU.ne',hA.ne']
    <;> ring

theorem cap_sum {N U A : ℝ} (hN : 0<N) (hU : 0<U) (hA : 0<A)
    (q : ℕ) (hq : (q : ℝ)≤N/A) :
    (∑d∈Finset.Icc 1 q,min U (N/(d : ℝ)))≤N*Area (U/A) := by
  have hf : AntitoneOn (Cap N U) (Icc (0 : ℝ) q) := (cap_antitone hN hU).antitoneOn _
  have hs := AntitoneOn.sum_le_integral (a := q) (x₀ := 0) (f := Cap N U) (by simpa using hf)
  have he : (∑d∈Finset.Icc 1 q,min U (N/(d : ℝ)))=
      ∑i∈Finset.range q,Cap N U ((i+1 : ℕ) : ℝ) := by
    have hh:=Finset.sum_Ico_add (fun d : ℕ=>min U (N/(d : ℝ))) 0 q 1
    rw [Nat.Ico_zero_eq_range,Nat.zero_add,Finset.Ico_add_one_right_eq_Icc] at hh
    rw [←hh]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [Nat.cast_add,Nat.cast_one,Nat.add_comm] using
      (cap_eq_min hN hU (show (0 : ℝ)<((i+1 : ℕ) : ℝ) by positivity)).symm
  have hint : (∫x in (0 : ℝ)..q,Cap N U x)≤∫x in (0 : ℝ)..N/A,Cap N U x := by
    apply integral_mono_interval le_rfl (by positivity) hq ?_ ((cap_continuous hN hU).intervalIntegrable 0 (N/A))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact cap_nonneg hN hU x
  rw [he,←cap_integral hN hU hA]
  have hs' : (∑i∈Finset.range q,Cap N U ((i+1 : ℕ) : ℝ))≤∫x in (0 : ℝ)..q,Cap N U x := by
    simpa only [zero_add] using hs
  exact hs'.trans hint

theorem area_tangent {r : ℝ} (hr : 0<r) (j : ℕ) : Area r≤Tangent r j := by
  by_cases hr1 : r≤1
  · rw [Area,if_pos hr1]
    cases j with
    | zero => simp [Tangent]
    | succ j =>
      by_cases hj : j=0
      · subst j
        norm_num [Tangent]
        linarith only [hr1]
      · have hj2 : (2 : ℝ)≤((j+1 : ℕ) : ℝ) := by exact_mod_cast (show 2≤j+1 by omega)
        have hfirst : (1 : ℝ)≤((j+1 : ℕ) : ℝ)*(173287/250000 : ℝ) := by nlinarith only [hj2]
        have htail : (0 : ℝ)≤r/(2 : ℝ)^(j+1) := by positivity
        dsimp only [Tangent]
        linarith only [hr1,hfirst,htail]
  · have hp : (0 : ℝ)<(2 : ℝ)^j := by positivity
    have hl:=Real.log_le_sub_one_of_pos (div_pos hr hp)
    rw [Real.log_div hr.ne' hp.ne',Real.log_pow] at hl
    have hlog:=mul_le_mul_of_nonneg_left HarmonicLog55.actual_log_two_upper (Nat.cast_nonneg j)
    rw [Area,if_neg hr1]
    dsimp only [Tangent]
    linarith only [hl,hlog]

theorem clipped_sum {N U A q : ℕ} (hN : 0<N) (hU : 0<U) (hA : 0<A) (hq : q≤N/A) :
    ((∑d∈Finset.Icc 1 q,min U (N/d+1) : ℕ) : ℝ)≤
      (N : ℝ)*(Area ((U : ℝ)/A)+1/(A : ℝ)) := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hUR : (0 : ℝ)<U := by exact_mod_cast hU
  have hAR : (0 : ℝ)<A := by exact_mod_cast hA
  have hqR : (q : ℝ)≤(N : ℝ)/A := by
    apply (le_div_iff₀ hAR).mpr
    exact_mod_cast (Nat.le_div_iff_mul_le hA).mp hq
  have hs : ((∑d∈Finset.Icc 1 q,min U (N/d+1) : ℕ) : ℝ)≤
      (∑d∈Finset.Icc 1 q,min (U : ℝ) ((N : ℝ)/d))+(q : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _≤∑d∈Finset.Icc 1 q,(min (U : ℝ) ((N : ℝ)/d)+1) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdR : (0 : ℝ)<d := by exact_mod_cast (show 0<d by have := (Finset.mem_Icc.mp hd).1;omega)
        have hdiv : ((N/d : ℕ) : ℝ)≤(N : ℝ)/d := by
          apply (le_div_iff₀ hdR).mpr
          exact_mod_cast Nat.div_mul_le_self N d
        by_cases hu : (U : ℝ)≤(N : ℝ)/d
        · rw [min_eq_left hu]
          have hh : ((min U (N/d+1) : ℕ) : ℝ)≤(U : ℝ) := by exact_mod_cast min_le_left U (N/d+1)
          linarith only [hh]
        · rw [min_eq_right (le_of_lt (lt_of_not_ge hu))]
          have hh : ((min U (N/d+1) : ℕ) : ℝ)≤((N/d : ℕ) : ℝ)+1 := by exact_mod_cast min_le_right U (N/d+1)
          linarith only [hh,hdiv]
      _=_ := by simp [Finset.sum_add_distrib]
  have hc:=cap_sum hNR hUR hAR q hqR
  calc
    _≤(N : ℝ)*Area ((U : ℝ)/A)+(q : ℝ) := by linarith only [hs,hc]
    _≤(N : ℝ)*Area ((U : ℝ)/A)+(N : ℝ)/A := by linarith only [hqR]
    _=_ := by ring

theorem clipped_sum_tangent {N U A q : ℕ} (hN : 0<N) (hU : 0<U) (hA : 0<A) (hq : q≤N/A) (j : ℕ) :
    ((∑d∈Finset.Icc 1 q,min U (N/d+1) : ℕ) : ℝ)≤
      (N : ℝ)*(Tangent ((U : ℝ)/A) j+1/(A : ℝ)) := by
  have hr : (0 : ℝ)<(U : ℝ)/A := div_pos (by exact_mod_cast hU) (by exact_mod_cast hA)
  exact (clipped_sum hN hU hA hq).trans
    (mul_le_mul_of_nonneg_left (by linarith only [area_tangent hr j]) (Nat.cast_nonneg N))

#print axioms cap_integral
#print axioms cap_sum
#print axioms area_tangent
#print axioms clipped_sum_tangent
end
end JSP233.CleanupIntegral209
