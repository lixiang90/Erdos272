module

public import Erdos272.Core.N200000.PrimeQuadratic200000
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Quantitative bounded-domain union source. A short dyadic range is
used first; the existing coarse estimate pays the larger core lengths. -/
namespace JSP233.QuantitativeUnit200000
open CoreUnionSource200000 PrimeQuadratic200000 DyadicReciprocal200000 APInterval208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem unit_quadratic_dyadic {a k : ℕ} (ha : a ≤ 2 ^ k) :
    (a : ℝ) ^ 2 / 4 - ((k : ℝ) + 1) / 2 * a ≤ (UnitBound a : ℝ) := by
  have hs := Finset.sum_le_sum (s := AllPrimes a) (fun q hq =>
    twice_weight_bound a (Finset.mem_filter.mp hq).2.pos)
  have hs' : 2 * ((∑ q ∈ AllPrimes a, Weight a q : ℕ) : ℝ) ≤
      (a : ℝ) ^ 2 * (∑ q ∈ AllPrimes a, (1 : ℝ) / (q : ℝ) ^ 2) +
        (a : ℝ) * (∑ q ∈ AllPrimes a, (1 : ℝ) / (q : ℝ)) := by
    simpa only [Nat.cast_sum, Finset.mul_sum, Finset.sum_add_distrib] using hs
  have hsq := mul_le_mul_of_nonneg_left (prime_square_sum a) (sq_nonneg (a : ℝ))
  have hrec := mul_le_mul_of_nonneg_left (prime_reciprocal ha) (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hnat : a.choose 2 ≤ UnitBound a + ∑ q ∈ AllPrimes a, Weight a q := by unfold UnitBound; omega
  have hnatR : (a.choose 2 : ℝ) ≤ (UnitBound a : ℝ) + ((∑ q ∈ AllPrimes a, Weight a q : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hchoose : 2 * (a.choose 2 : ℝ) + (a : ℝ) = (a : ℝ) * a := by exact_mod_cast choose_two_twice a
  nlinarith only [hs', hsq, hrec, hnatR, hchoose]

theorem unit_floor {a t k lower : ℕ} (hlarge : t ≤ a) (hcap : a ≤ 2 ^ k)
    (hmono : k + 1 ≤ t) (hvalue : 4 * lower + 2 * (k + 1) * t ≤ t * t) :
    lower ≤ UnitBound a := by
  have hq := unit_quadratic_dyadic hcap
  have haR : (t : ℝ) ≤ a := by exact_mod_cast hlarge
  have htR : (k : ℝ) + 1 ≤ t := by exact_mod_cast hmono
  have hp : 0 ≤ ((a : ℝ) - t) * ((a : ℝ) + t - 2 * ((k : ℝ) + 1)) :=
    mul_nonneg (sub_nonneg.mpr haR) (by linarith only [haR, htR])
  have hvR : 4 * (lower : ℝ) + 2 * ((k : ℝ) + 1) * t ≤ (t : ℝ) * t := by
    exact_mod_cast hvalue
  have hlR : (lower : ℝ) ≤ (UnitBound a : ℝ) := by nlinarith only [hq, hp, hvR]
  exact_mod_cast hlR

#print axioms unit_quadratic_dyadic
#print axioms unit_floor
end
end JSP233.QuantitativeUnit200000
