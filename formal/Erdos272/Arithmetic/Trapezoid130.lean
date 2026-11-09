module

public import Erdos272.Arithmetic.VolumeStep125
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace JSP233.Trapezoid130
open Set MeasureTheory intervalIntegral
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem chord_bound {f : ℝ→ℝ} {a b t : ℝ}
    (hab : a<b) (hf : ConvexOn ℝ (Icc a b) f) (ht : t∈Icc a b) :
    f t≤(b-t)/(b-a)*f a+(t-a)/(b-a)*f b := by
  have hd : 0<b-a := sub_pos.mpr hab
  have hs : (b-t)/(b-a)+(t-a)/(b-a)=1 := by field_simp; ring
  have he : (b-t)/(b-a)*a+(t-a)/(b-a)*b=t := by field_simp; ring
  have h := hf.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
    (div_nonneg (sub_nonneg.mpr ht.2) hd.le)
    (div_nonneg (sub_nonneg.mpr ht.1) hd.le) hs
  simpa only [smul_eq_mul,he] using h

theorem integral_trapezoid {f : ℝ→ℝ} {a b : ℝ} (hab : a≤b)
    (hc : ContinuousOn f (Icc a b)) (hf : ConvexOn ℝ (Icc a b) f) :
    (∫t in a..b,f t)≤(b-a)*(f a+f b)/2 := by
  rcases eq_or_lt_of_le hab with rfl|hab
  · simp
  let g : ℝ→ℝ := fun t=>(b-t)/(b-a)*f a+(t-a)/(b-a)*f b
  have hgc : Continuous g := by fun_prop
  have hif : IntervalIntegrable f volume a b := hc.intervalIntegrable_of_Icc hab.le
  have hig : IntervalIntegrable g volume a b := hgc.intervalIntegrable a b
  have hi := integral_mono_on hab.le hif hig (fun t ht=>chord_bound hab hf ht)
  have he : (∫t in a..b,g t)=(b-a)*(f a+f b)/2 := by
    have hg : g=fun t=>t*((f b-f a)/(b-a))+(b*f a-a*f b)/(b-a) := by
      funext t
      dsimp only [g]
      ring
    rw [hg,intervalIntegral.integral_add (intervalIntegrable_id.mul_const _) intervalIntegrable_const,
      intervalIntegral.integral_mul_const,integral_id,intervalIntegral.integral_const,smul_eq_mul]
    field_simp
    ring
  exact hi.trans he.le

theorem integral_trapezoid_nat (q : ℕ) (hq : 1≤q) (f : ℝ→ℝ)
    (hc : ContinuousOn f (Icc (1:ℝ) q)) (hf : ConvexOn ℝ (Icc (1:ℝ) q) f) :
    (∫t in (1:ℝ)..q,f t)+f 1/2+f q/2≤∑a∈Finset.Icc 1 q,f a := by
  have H : ∀q:ℕ,1≤q→∀ (hc : ContinuousOn f (Icc (1:ℝ) q))
      (hf : ConvexOn ℝ (Icc (1:ℝ) q) f),
      (∫t in (1:ℝ)..q,f t)+f 1/2+f q/2≤∑a∈Finset.Icc 1 q,f a := by
    intro q hq
    induction q,hq using Nat.le_induction with
    | base =>
      intro _ _
      norm_num
    | succ q hq ih =>
      intro hc hf
      have hqR : (1:ℝ)≤q := by exact_mod_cast hq
      have hqs : (q:ℝ)≤(q+1:ℕ) := by exact_mod_cast Nat.le_succ q
      have h1s : (1:ℝ)≤(q+1:ℕ) := hqR.trans hqs
      have hs1 : Icc (1:ℝ) q⊆Icc (1:ℝ) (q+1:ℕ) := Icc_subset_Icc le_rfl hqs
      have hs2 : Icc (q:ℝ) (q+1:ℕ)⊆Icc (1:ℝ) (q+1:ℕ) := Icc_subset_Icc hqR le_rfl
      have hprev := ih (hc.mono hs1) (hf.subset hs1 (convex_Icc _ _))
      have hlast := integral_trapezoid hqs (hc.mono hs2) (hf.subset hs2 (convex_Icc _ _))
      have hi1 : IntervalIntegrable f volume (1:ℝ) q := (hc.mono hs1).intervalIntegrable_of_Icc hqR
      have hi2 : IntervalIntegrable f volume (q:ℝ) (q+1:ℕ) := (hc.mono hs2).intervalIntegrable_of_Icc hqs
      have he := integral_add_adjacent_intervals hi1 hi2
      rw [Finset.sum_Icc_succ_top (by omega : 1≤q+1)]
      push_cast at hlast he ⊢
      linarith only [hprev,hlast,he]
  exact H q hq hc hf

#print axioms chord_bound
#print axioms integral_trapezoid
#print axioms integral_trapezoid_nat
end
end JSP233.Trapezoid130
