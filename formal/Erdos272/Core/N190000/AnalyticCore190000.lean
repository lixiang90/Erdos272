module

public import Erdos272.Arithmetic.N190000.PrimeHead190000
public import Erdos272.Core.N200000.MixedCore200000

@[expose] public section

namespace JSP233.AnalyticCore190000
open CoreUnionSource200000 PrimeQuadratic200000 PrimeHead190000 DyadicReciprocal200000
open StarCompletion SourceBridge208 IntrinsicTriples208 SourceFloorSound291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem unit_quadratic {a : ℕ} {r : ℝ}
    (hr : (∑ q ∈ AllPrimes a, (1 : ℝ)/(q : ℝ)) ≤ r) :
    (21/80 : ℝ)*(a : ℝ)^2-(r+1)/2*a ≤ (UnitBound a : ℝ) := by
  have hs := Finset.sum_le_sum (s := AllPrimes a) (fun q hq =>
    twice_weight_bound a (Finset.mem_filter.mp hq).2.pos)
  have hs' : 2*((∑ q ∈ AllPrimes a, Weight a q : ℕ) : ℝ) ≤
      (a : ℝ)^2*(∑ q ∈ AllPrimes a, (1 : ℝ)/(q : ℝ)^2)+
      (a : ℝ)*(∑ q ∈ AllPrimes a, (1 : ℝ)/(q : ℝ)) := by
    simpa only [Nat.cast_sum, Finset.mul_sum, Finset.sum_add_distrib] using hs
  have hsq := mul_le_mul_of_nonneg_left (prime_square_sum_sharp a) (sq_nonneg (a : ℝ))
  have hrec := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hn : a.choose 2 ≤ UnitBound a+∑ q ∈ AllPrimes a, Weight a q := by unfold UnitBound; omega
  have hnR : (a.choose 2 : ℝ) ≤ (UnitBound a : ℝ)+((∑ q ∈ AllPrimes a, Weight a q : ℕ) : ℝ) := by
    exact_mod_cast hn
  have hc : 2*(a.choose 2 : ℝ)+(a : ℝ) = (a : ℝ)*a := by
    exact_mod_cast APInterval208.choose_two_twice a
  nlinarith only [hs', hsq, hrec, hnR, hc]

theorem unit_small {a : ℕ} (ha : a ≤ 256) :
    (21/80 : ℝ)*(a : ℝ)^2-(3/2 : ℝ)*a ≤ (UnitBound a : ℝ) := by
  convert unit_quadratic (small_reciprocal ha) using 1
  norm_num

theorem unit_large {a : ℕ} (ha : a ≤ 2^18) :
    (21/80 : ℝ)*(a : ℝ)^2-(19/2 : ℝ)*a ≤ (UnitBound a : ℝ) := by
  have hh := unit_quadratic (prime_reciprocal ha)
  norm_num only [Nat.cast_ofNat] at hh
  exact hh

theorem floor_small {a t u : ℕ} (hta : t ≤ a) (ha : a ≤ 256) (ht : 3 ≤ t)
    (hv : 80*u+120*t ≤ 21*t*t) : u ≤ UnitBound a := by
  have hq := unit_small ha
  have htaR : (t : ℝ) ≤ a := by exact_mod_cast hta
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hp : 0 ≤ ((a : ℝ)-t)*(21*((a : ℝ)+t)-120) :=
    mul_nonneg (sub_nonneg.mpr htaR) (by linarith only [htaR, htR])
  have hvR : 80*(u : ℝ)+120*t ≤ 21*(t : ℝ)*t := by exact_mod_cast hv
  have hu : (u : ℝ) ≤ UnitBound a := by nlinarith only [hq, hp, hvR]
  exact_mod_cast hu

theorem floor_large {a t u : ℕ} (hta : t ≤ a) (ha : a ≤ 2^18) (ht : 19 ≤ t)
    (hv : 80*u+760*t ≤ 21*t*t) : u ≤ UnitBound a := by
  have hq := unit_large ha
  have htaR : (t : ℝ) ≤ a := by exact_mod_cast hta
  have htR : (19 : ℝ) ≤ t := by exact_mod_cast ht
  have hp : 0 ≤ ((a : ℝ)-t)*(21*((a : ℝ)+t)-760) :=
    mul_nonneg (sub_nonneg.mpr htaR) (by linarith only [htaR, htR])
  have hvR : 80*(u : ℝ)+760*t ≤ 21*(t : ℝ)*t := by exact_mod_cast hv
  have hu : (u : ℝ) ≤ UnitBound a := by nlinarith only [hq, hp, hvR]
  exact_mod_cast hu

theorem floor_split {a t u : ℕ} (hta : t ≤ a) (ha : a ≤ 2^18) (ht : 3 ≤ t)
    (hv : 80*u+120*t ≤ 21*t*t) (htail : 80*u+760*257 ≤ 21*257*257) :
    u ≤ UnitBound a := by
  by_cases hs : a ≤ 256
  · exact floor_small hta hs ht hv
  · exact floor_large (t := 257) (by omega) ha (by decide) htail

abbrev Plan := MixedCore200000.Plan

def Conditions (q : Plan) : Prop :=
  q.cutoff ≤ q.lower ∧
  ((q.unit = 0 ∧ q.cutoff = q.defect) ∨
    (q.target ≤ q.defect*q.unit ∧
      ((3 ≤ q.lower-q.cutoff+1 ∧
        80*q.unit+120*(q.lower-q.cutoff+1) ≤ 21*(q.lower-q.cutoff+1)^2 ∧
        80*q.unit+760*257 ≤ 21*257*257) ∨
       (19 ≤ q.lower-q.cutoff+1 ∧
        80*q.unit+760*(q.lower-q.cutoff+1) ≤ 21*(q.lower-q.cutoff+1)^2))))

instance (q : Plan) : Decidable (Conditions q) := by unfold Conditions; infer_instance

theorem actual_plan_source {N : ℕ} {S : Finset ℤ} (q : Plan)
    (hq : Conditions q) (hf : Floor q.lower q.cutoff q.target)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : q.lower ≤ S.card) (hdefect : q.defect ≤ Defect S) :
    q.target ≤ (Pool S).card := by
  rcases hq.2 with hlegacy | hmixed
  · have hcard : S.card ≤ N := by simpa only [ground_card] using Finset.card_le_card hground
    exact (hf S.card hsize (by norm_num at *; omega)).trans
      (actual_source_of_defect hS (by simpa only [hlegacy.2] using hdefect))
  · apply MixedCore200000.actual_mixed_source hN hground hS hsize hdefect hq.1 hf _ hmixed.1
    intro a hlo hhi
    rcases hmixed.2 with hs | hl
    · exact floor_split hlo hhi hs.1 (by simpa only [pow_two, mul_assoc] using hs.2.1) hs.2.2
    · exact floor_large hlo hhi hl.1 (by simpa only [pow_two, mul_assoc] using hl.2)

#print axioms unit_quadratic
#print axioms unit_small
#print axioms unit_large
#print axioms floor_small
#print axioms floor_large
#print axioms floor_split
#print axioms actual_plan_source
end
end JSP233.AnalyticCore190000
