import Erdos272.Arithmetic.Trapezoid130
import Mathlib.Analysis.Convex.Deriv
namespace JSP233.ConvexQuotient130
open Set MeasureTheory intervalIntegral
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem convex_from_derivative {s : Set ℝ} (hs : Convex ℝ s) {f g : ℝ→ℝ}
    (hd : ∀t∈s,HasDerivAt f (g t) t) (hg : MonotoneOn g s) : ConvexOn ℝ s f := by
  apply MonotoneOn.convexOn_of_deriv hs
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro u hu v hv huv
    rw [(hd u (interior_subset hu)).deriv,(hd v (interior_subset hv)).deriv]
    exact hg (interior_subset hu) (interior_subset hv) huv

theorem quotient_derivative {x t : ℝ} (ht : 0<t) :
    HasDerivAt (fun u:ℝ=>x/u) (-x/t^2) t := by
  simpa only [div_eq_mul_inv,mul_neg,neg_mul] using (hasDerivAt_inv ht.ne').const_mul x

theorem quotient_convex {x : ℝ} (hx : 0≤x) :
    ConvexOn ℝ (Ioi (0:ℝ)) (fun t:ℝ=>x/t) := by
  apply convex_from_derivative (convex_Ioi _) (fun t ht=>quotient_derivative ht)
  intro u hu v hv huv
  have hs : u^2≤v^2 := (sq_le_sq₀ hu.le hv.le).mpr huv
  have h := div_le_div_of_nonneg_left hx (sq_pos_of_pos hu) hs
  change -x/u^2≤-x/v^2
  simpa only [neg_div] using neg_le_neg h

theorem convex_comp_quotient {V : ℝ→ℝ} (hV : ConvexOn ℝ (Ici (1:ℝ)) V)
    (hm : MonotoneOn V (Ici (1:ℝ))) {x : ℝ} (hx : 1≤x) :
    ConvexOn ℝ (Icc (1:ℝ) x) (fun t:ℝ=>V (x/t)) := by
  have hrange : ∀t∈Icc (1:ℝ) x,(1:ℝ)≤x/t := by
    intro t ht
    exact (one_le_div (lt_of_lt_of_le zero_lt_one ht.1)).mpr ht.2
  have hquot := (quotient_convex (by linarith only [hx] : 0≤x)).subset
    (show Icc (1:ℝ) x⊆Ioi (0:ℝ) from fun t ht=>lt_of_lt_of_le zero_lt_one ht.1)
    (convex_Icc _ _)
  refine ⟨convex_Icc _ _,?_⟩
  intro u hu v hv a b ha hb hab
  have hmid : a • u+b • v∈Icc (1:ℝ) x := (convex_Icc _ _) hu hv ha hb hab
  have hsum : a • (x/u)+b • (x/v)∈Ici (1:ℝ) :=
    (convex_Ici _) (hrange u hu) (hrange v hv) ha hb hab
  exact (hm (hrange _ hmid) hsum (hquot.2 hu hv ha hb hab)).trans
    (hV.2 (hrange u hu) (hrange v hv) ha hb hab)

theorem continuous_comp_quotient {V g : ℝ→ℝ}
    (hd : ∀t∈Ici (1:ℝ),HasDerivAt V (g t) t) {x : ℝ} (_hx : 1≤x) :
    ContinuousOn (fun t:ℝ=>V (x/t)) (Icc (1:ℝ) x) := by
  intro t ht
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht.1
  have hquot : 1≤x/t := (one_le_div ht0).mpr ht.2
  exact ((hd (x/t) hquot).continuousAt.comp
    (quotient_derivative (x:=x) ht0).continuousAt).continuousWithinAt

#print axioms convex_from_derivative
#print axioms quotient_derivative
#print axioms quotient_convex
#print axioms convex_comp_quotient
#print axioms continuous_comp_quotient
end
end JSP233.ConvexQuotient130
