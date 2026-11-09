module

public import Erdos272.Arithmetic.Trapezoid130
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section
namespace JSP233.FloorTrapezoid130
open Trapezoid130 SimplexMoment57
open Set MeasureTheory intervalIntegral
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem integral_le_sum_floor_half {x : ℝ} (hx : 1≤x) (f : ℝ→ℝ)
    (hc : ContinuousOn f (Icc 1 x)) (hf : ConvexOn ℝ (Icc 1 x) f)
    (hfx : f x=0) (hfq : 0≤f (Nat.floor x)) :
    (∫t in (1:ℝ)..x,f t)+f 1/2≤∑a∈Finset.Icc 1 (Nat.floor x),f a := by
  let q := Nat.floor x
  have hq1 : 1≤q := (Nat.one_le_floor_iff x).mpr hx
  have hq1R : (1:ℝ)≤q := by exact_mod_cast hq1
  have hqx : (q:ℝ)≤x := Nat.floor_le (by linarith only [hx])
  have hxq : x<(q:ℝ)+1 := Nat.lt_floor_add_one x
  have hs1 : Icc (1:ℝ) q⊆Icc (1:ℝ) x := Icc_subset_Icc le_rfl hqx
  have hs2 : Icc (q:ℝ) x⊆Icc (1:ℝ) x := Icc_subset_Icc hq1R le_rfl
  have hfirst := integral_trapezoid_nat q hq1 f (hc.mono hs1)
    (hf.subset hs1 (convex_Icc _ _))
  have htail := integral_trapezoid hqx (hc.mono hs2) (hf.subset hs2 (convex_Icc _ _))
  rw [hfx,add_zero] at htail
  have hp := mul_le_mul_of_nonneg_right (show x-(q:ℝ)≤1 by linarith only [hxq]) hfq
  have hi1 : IntervalIntegrable f volume (1:ℝ) q := (hc.mono hs1).intervalIntegrable_of_Icc hq1R
  have hi2 : IntervalIntegrable f volume (q:ℝ) x := (hc.mono hs2).intervalIntegrable_of_Icc hqx
  have he := integral_add_adjacent_intervals hi1 hi2
  linarith only [hfirst,htail,hp,he]

theorem count_step_half (k : ℕ) (V W : ℝ→ℝ)
    (hmono : MonotoneOn V (Ici (1:ℝ))) (hV1 : V 1=0)
    (hcontinuous : ∀x:ℝ,1≤x→ContinuousOn (fun t:ℝ=>V (x/t)) (Icc 1 x))
    (hconvex : ∀x:ℝ,1≤x→ConvexOn ℝ (Icc 1 x) (fun t:ℝ=>V (x/t)))
    (hlower : ∀x:ℝ,1≤x→V x≤(DivCount k (Nat.floor x):ℝ))
    (hint : ∀x:ℝ,1≤x→(∫t in (1:ℝ)..x,V (x/t))+V x/2=W x)
    {x : ℝ} (hx : 1≤x) : W x≤(DivCount (k+1) (Nat.floor x):ℝ) := by
  have hqx : ((Nat.floor x):ℝ)≤x := Nat.floor_le (by linarith only [hx])
  have hqpos : (0:ℝ)<Nat.floor x := Nat.cast_pos.mpr ((Nat.one_le_floor_iff x).mpr hx)
  have hquot : (1:ℝ)≤x/(Nat.floor x) := (one_le_div hqpos).mpr hqx
  have hfq : 0≤V (x/(Nat.floor x)) := by
    have h := hmono (by norm_num : (1:ℝ)∈Ici 1) hquot hquot
    rwa [hV1] at h
  have hi := integral_le_sum_floor_half hx (fun t:ℝ=>V (x/t))
    (hcontinuous x hx) (hconvex x hx) (by rw [div_self (by linarith only [hx] : x≠0),hV1]) hfq
  simp only [div_one] at hi
  rw [hint x hx] at hi
  have hs : (∑a∈Finset.Icc 1 (Nat.floor x),V (x/(a:ℝ)))≤
      ∑a∈Finset.Icc 1 (Nat.floor x),(DivCount k (Nat.floor (x/(a:ℝ))):ℝ) := by
    apply Finset.sum_le_sum
    intro a ha
    obtain ⟨ha1,haq⟩ := Finset.mem_Icc.mp ha
    have ha0 : (0:ℝ)<a := Nat.cast_pos.mpr ha1
    have hax : (a:ℝ)≤x := (Nat.cast_le.mpr haq).trans hqx
    exact hlower (x/(a:ℝ)) ((one_le_div ha0).mpr hax)
  have he : (∑a∈Finset.Icc 1 (Nat.floor x),(DivCount k (Nat.floor (x/(a:ℝ))):ℝ))=
      (DivCount (k+1) (Nat.floor x):ℝ) := by
    simp only [DivCount,Nat.cast_sum,Nat.floor_div_natCast]
  exact hi.trans (hs.trans he.le)

#print axioms integral_le_sum_floor_half
#print axioms count_step_half
end
end JSP233.FloorTrapezoid130
