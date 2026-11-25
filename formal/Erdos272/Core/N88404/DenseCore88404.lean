module

public import Erdos272.Arithmetic.N88404.PrimeSquare88404
public import Erdos272.Counting.N118533.DenseBonus118533

@[expose] public section

namespace JSP233.DenseCore88404
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208 CoreUnionSource200000
open PrimeQuadratic200000 StarArithmetic130000 CorrelatedSource118533
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def CorePrice (a : ℝ) : ℝ := (2977/10000 : ℝ)*a^2-6*a+8

theorem unit_quadratic_of_bounds {a : ℕ} {sigma r : ℝ}
    (hsquare : (∑ q∈AllPrimes a, (1 : ℝ)/(q : ℝ)^2) ≤ sigma)
    (hreciprocal : (∑ q∈AllPrimes a, (1 : ℝ)/(q : ℝ)) ≤ r) :
    ((1-sigma)/2)*(a : ℝ)^2-((r+1)/2)*a ≤ (UnitBound a : ℝ) := by
  have hs := Finset.sum_le_sum (s := AllPrimes a) (fun q hq =>
    twice_weight_bound a (Finset.mem_filter.mp hq).2.pos)
  have hs' : 2*((∑ q∈AllPrimes a, Weight a q : ℕ) : ℝ) ≤
      (a : ℝ)^2*(∑ q∈AllPrimes a, (1 : ℝ)/(q : ℝ)^2)+
        (a : ℝ)*(∑ q∈AllPrimes a, (1 : ℝ)/(q : ℝ)) := by
    simpa only [Nat.cast_sum, Finset.mul_sum, Finset.sum_add_distrib] using hs
  have hsq := mul_le_mul_of_nonneg_left hsquare (sq_nonneg (a : ℝ))
  have hr := mul_le_mul_of_nonneg_left hreciprocal (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hn : a.choose 2 ≤ UnitBound a+∑ q∈AllPrimes a, Weight a q := by
    unfold UnitBound
    omega
  have hnR : (a.choose 2 : ℝ) ≤ (UnitBound a : ℝ)+((∑ q∈AllPrimes a, Weight a q : ℕ) : ℝ) := by
    exact_mod_cast hn
  have hc : 2*(a.choose 2 : ℝ)+(a : ℝ) = (a : ℝ)*a := by
    exact_mod_cast APInterval208.choose_two_twice a
  nlinarith only [hs', hsq, hr, hnR, hc]

theorem unit_large {a : ℕ} (ha : a≤2^18) :
    (547/2000 : ℝ)*(a : ℝ)^2-(21/4 : ℝ)*a ≤ (UnitBound a : ℝ) := by
  have hh := unit_quadratic_of_bounds (PrimeSquare88404.prime_square_sum a)
    (PrimeReciprocal180000.prime_reciprocal_half ha (by decide : 1≤18))
  norm_num only [Nat.cast_ofNat] at hh
  convert hh using 1 <;> norm_num

theorem combined_quadratic {a : ℕ} (ha : 92≤a) (hcap : a≤2^18) :
    CorePrice (a : ℝ) ≤ (UnitBound a+Bonus Primes a : ℕ) := by
  have hu := unit_large hcap
  have hb := DenseBonus118533.bonus_quadratic ha
  push_cast
  unfold CorePrice
  linarith only [hu, hb]

theorem core_ge_self {a : ℝ} (ha : 92≤a) : a≤CorePrice a := by
  have hc : 0≤(2977/10000 : ℝ)*(a+92)-7 := by linarith only [ha]
  have hm := mul_nonneg (sub_nonneg.mpr ha) hc
  unfold CorePrice
  nlinarith only [hm]

theorem core_growth {a k : ℝ} (ha : 92≤a) (hk : 0≤k) (hsmall : 47*k≤a) :
    CorePrice (a+k) ≤ CorePrice a+k*a := by
  have hc : (2*(2977/10000) : ℝ)*a+(2977/10000)*k-6≤a := by
    linarith only [ha, hsmall]
  have hm := mul_le_mul_of_nonneg_left hc hk
  unfold CorePrice
  nlinarith only [hm]

theorem core_coupling {a d : ℝ} (ha : 92≤a) (hd : 1≤d) (hsmall : 47*d≤a) :
    CorePrice (a+d-1) ≤ d*CorePrice a := by
  have hk : 0≤d-1 := by linarith only [hd]
  have hg := core_growth ha hk (by linarith only [hsmall] : 47*(d-1)≤a)
  have he : a+(d-1)=a+d-1 := by ring
  rw [he] at hg
  have hm := mul_le_mul_of_nonneg_left (core_ge_self ha) hk
  nlinarith only [hg, hm]

theorem actual_core_price {N : ℕ} {S : Finset ℤ}
    (hN : N≤2^18) (hground : S⊆Ground N) (hS : 2≤S.card) (ha : 92≤MaxAPSize S) :
    (Defect S : ℝ)*CorePrice (MaxAPSize S : ℝ) ≤ ((Pool S).card : ℝ) := by
  have hcard : S.card≤N := by simpa only [ground_card] using Finset.card_le_card hground
  have hcap : MaxAPSize S≤2^18 := (maxAPSize_le_card S).trans (hcard.trans hN)
  have hu := combined_quadratic ha hcap
  have hstar := actual_eight_star_source hN hground hS (by omega : 12≤MaxAPSize S)
  have hm := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℝ) (Defect S))
  have hstarR : (Defect S : ℝ)*(UnitBound (MaxAPSize S)+Bonus Primes (MaxAPSize S) : ℕ) ≤
      ((Pool S).card : ℝ) := by exact_mod_cast hstar
  exact hm.trans hstarR

#print axioms unit_quadratic_of_bounds
#print axioms unit_large
#print axioms combined_quadratic
#print axioms core_ge_self
#print axioms core_growth
#print axioms core_coupling
#print axioms actual_core_price
end
end JSP233.DenseCore88404
