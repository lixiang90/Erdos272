module

public import Erdos272.Arithmetic.SimplexMoment57
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.VolumeLower125
open SimplexMoment57 HarmonicAbel29
open scoped Classical BigOperators
open Set MeasureTheory intervalIntegral
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def V1 (x : ℝ) : ℝ := x-1
def V2 (x : ℝ) : ℝ := x*Real.log x-x+1
def V3 (x : ℝ) : ℝ := x*((Real.log x)^2/2-Real.log x+1)-1
def V4 (x : ℝ) : ℝ := x*((Real.log x)^3/6-(Real.log x)^2/2+Real.log x-1)+1

theorem integral_le_sum_floor {x : ℝ} (hx : 1≤x) (f : ℝ→ℝ)
    (hf : AntitoneOn f (Icc 1 x)) (hfq : 0≤f (Nat.floor x)) :
    (∫t in (1:ℝ)..x,f t)≤∑a∈Finset.Icc 1 (Nat.floor x),f a := by
  let q := Nat.floor x
  have hq1 : 1≤q := (Nat.one_le_floor_iff x).mpr hx
  have hq1R : (1:ℝ)≤q := by exact_mod_cast hq1
  have hqx : (q:ℝ)≤x := Nat.floor_le (by linarith only [hx])
  have hxq : x<(q:ℝ)+1 := Nat.lt_floor_add_one x
  have hfirst : AntitoneOn f (Icc (1:ℝ) q) :=
    hf.mono (Icc_subset_Icc le_rfl hqx)
  have htail : AntitoneOn f (Icc (q:ℝ) x) :=
    hf.mono (Icc_subset_Icc hq1R le_rfl)
  have hi1 : IntervalIntegrable f volume (1:ℝ) q :=
    (show AntitoneOn f (uIcc (1:ℝ) q) by rwa [uIcc_of_le hq1R]).intervalIntegrable
  have hi2 : IntervalIntegrable f volume (q:ℝ) x :=
    (show AntitoneOn f (uIcc (q:ℝ) x) by rwa [uIcc_of_le hqx]).intervalIntegrable
  have hfirstNat : AntitoneOn f (Icc ((1:ℕ):ℝ) q) := by simpa only [Nat.cast_one] using hfirst
  have hs := AntitoneOn.integral_le_sum_Ico (f:=f) hq1 hfirstNat
  norm_num only [Nat.cast_one] at hs
  have ht : (∫t in (q:ℝ)..x,f t)≤f q := by
    have hb := integral_mono_on hqx hi2 (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>f q) volume q x)
      (by intro t ht;exact hf ⟨hq1R,hqx⟩ ⟨hq1R.trans ht.1,ht.2⟩ ht.1)
    have hp := mul_le_mul_of_nonneg_right (show x-(q:ℝ)≤1 by linarith only [hxq]) hfq
    rw [intervalIntegral.integral_const,smul_eq_mul] at hb
    exact hb.trans (by simpa only [one_mul] using hp)
  have he := integral_add_adjacent_intervals hi1 hi2
  have hsum : (∑a∈Finset.Icc 1 q,f (a:ℝ))=(∑a∈Finset.Ico 1 q,f (a:ℝ))+f q := by
    simpa only [Finset.Ico_add_one_right_eq_Icc] using
      (Finset.sum_Ico_succ_top (f:=fun a:ℕ=>f (a:ℝ)) hq1)
  rw [hsum]
  linarith only [hs,ht,he]

theorem v1_derivative (x : ℝ) : HasDerivAt V1 1 x := by
  change HasDerivAt (fun y:ℝ=>y-1) (1:ℝ) x
  convert (hasDerivAt_id x).sub_const 1 using 1 <;> rfl

theorem v2_derivative {x : ℝ} (hx : 0<x) : HasDerivAt V2 (Real.log x) x := by
  have hd := (((hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')).sub (hasDerivAt_id x)).add_const 1
  convert hd using 1 <;> first | rfl | (change Real.log x=1*Real.log x+x*x⁻¹-1;rw [mul_inv_cancel₀ hx.ne'];ring)

theorem v3_derivative {x : ℝ} (hx : 0<x) : HasDerivAt V3 ((Real.log x)^2/2) x := by
  have hl := Real.hasDerivAt_log hx.ne'
  have hp := (((hl.pow 2).div_const 2).sub hl).add_const 1
  have hd := ((hasDerivAt_id x).mul hp).sub_const 1
  convert hd using 1 <;> first | rfl | (simp only [Pi.sub_apply,Pi.pow_apply,id_eq];field_simp [hx.ne'];ring)

theorem monotone_from_derivative {f g : ℝ→ℝ}
    (hd : ∀x∈Ici (1:ℝ),HasDerivAt f (g x) x)
    (hg : ∀x∈Ici (1:ℝ),0≤g x) : MonotoneOn f (Ici (1:ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact hg x (interior_subset hx)

theorem v1_monotone : MonotoneOn V1 (Ici (1:ℝ)) := by
  apply monotone_from_derivative (fun x _hx=>v1_derivative x)
  intro x hx
  norm_num

theorem v2_monotone : MonotoneOn V2 (Ici (1:ℝ)) := by
  apply monotone_from_derivative (fun x hx=>v2_derivative (lt_of_lt_of_le zero_lt_one hx))
  intro x hx
  exact Real.log_nonneg hx

theorem v3_monotone : MonotoneOn V3 (Ici (1:ℝ)) := by
  apply monotone_from_derivative (fun x hx=>v3_derivative (lt_of_lt_of_le zero_lt_one hx))
  intro x hx
  positivity

#print axioms integral_le_sum_floor
#print axioms v1_derivative
#print axioms v2_derivative
#print axioms v3_derivative
#print axioms monotone_from_derivative
#print axioms v1_monotone
#print axioms v2_monotone
#print axioms v3_monotone
end
end JSP233.VolumeLower125
