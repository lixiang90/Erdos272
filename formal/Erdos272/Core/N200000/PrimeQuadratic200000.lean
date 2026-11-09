module

public import Erdos272.Core.N200000.DyadicReciprocal200000
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-! Coarse elementary prime reciprocal estimates pay the large-size
source tail. Only finite sums in the actual bounded size domain are used. -/
namespace JSP233.PrimeQuadratic200000
open StarCompletion APGeometry SourceBridge208 CoreUnionSource200000 DyadicReciprocal200000 APInterval208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def OddSet (a : ℕ) : Finset ℕ := (Finset.range a).image (fun j : ℕ => 2 * j + 3)

theorem all_primes_subset_odd (a : ℕ) : AllPrimes a ⊆ insert 2 (OddSet a) := by
  intro q hq
  obtain ⟨hr, hp⟩ := Finset.mem_filter.mp hq
  by_cases htwo : q = 2
  · exact Finset.mem_insert.mpr (Or.inl htwo)
  · have hodd : q % 2 = 1 := hp.eq_two_or_odd.resolve_left htwo
    have hq2 := hp.two_le
    let j := (q - 3) / 2
    have he : 2 * j + 3 = q := by dsimp only [j]; omega
    have hj : j < a := by have := Finset.mem_range.mp hr; dsimp only [j]; omega
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, he⟩))

theorem prime_square_sum (a : ℕ) :
    (∑ q ∈ AllPrimes a, (1 : ℝ) / (q : ℝ) ^ 2) ≤ 1 / 2 := by
  have hs : (∑ q ∈ AllPrimes a, (1 : ℝ) / (q : ℝ) ^ 2) ≤
      ∑ q ∈ insert 2 (OddSet a), (1 : ℝ) / (q : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (all_primes_subset_odd a) (fun _ _ _ => by positivity)
  have htwo : 2 ∉ OddSet a := by
    intro hh
    obtain ⟨j, _hj, he⟩ := Finset.mem_image.mp hh
    omega
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 3) := by
    intro i j he
    change 2 * i + 3 = 2 * j + 3 at he
    omega
  have hsum : (∑ q ∈ OddSet a, (1 : ℝ) / (q : ℝ) ^ 2) =
      ∑ j ∈ Finset.range a, (1 : ℝ) / (2 * (j : ℝ) + 3) ^ 2 := by
    rw [OddSet, Finset.sum_image hinj.injOn]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [Finset.sum_insert htwo, hsum] at hs
  norm_num at hs
  have ho := odd_square_sum a
  simp only [one_div] at ho ⊢
  linarith only [hs, ho]

theorem twice_weight_bound (a : ℕ) {q : ℕ} (hq : 0 < q) :
    2 * (Weight a q : ℝ) ≤ (a : ℝ) ^ 2 * (1 / (q : ℝ) ^ 2) + (a : ℝ) * (1 / (q : ℝ)) := by
  let m := (a + q - 1) / q
  by_cases hmzero : m = 0
  · have hw : Weight a q = 0 := by change m.choose 2 = 0; simp only [hmzero, Nat.choose_zero_succ]
    rw [hw, Nat.cast_zero, mul_zero]
    positivity
  · have hmpos : 1 ≤ m := Nat.pos_of_ne_zero hmzero
    have hmSub : m - 1 + 1 = m := Nat.sub_add_cancel hmpos
    have hmq : m * q ≤ a + q - 1 := Nat.div_mul_le_self _ _
    have hmq' : m * q ≤ a + q := hmq.trans (Nat.sub_le _ _)
    have hprevEq : (m - 1) * q + q = m * q := by
      have hh := congrArg (fun z : ℕ => z * q) hmSub
      simpa only [Nat.add_mul, one_mul] using hh
    have hprev : (m - 1) * q ≤ a := by omega
    have hprod := Nat.mul_le_mul hmq' hprev
    have hchoose := choose_two_twice m
    have hmprod : m * (m - 1) + m = m * m := by
      have hh := congrArg (fun z : ℕ => m * z) hmSub
      simpa only [Nat.mul_add, mul_one] using hh
    have htwo : 2 * m.choose 2 = m * (m - 1) := by omega
    have hnat : 2 * Weight a q * q * q ≤ a * a + a * q := by
      change 2 * m.choose 2 * q * q ≤ _
      rw [htwo]
      nlinarith only [hprod]
    have hreal : 2 * (Weight a q : ℝ) * (q : ℝ) * (q : ℝ) ≤ (a : ℝ) * a + (a : ℝ) * q := by
      exact_mod_cast hnat
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    have he : (a : ℝ) ^ 2 * (1 / (q : ℝ) ^ 2) + (a : ℝ) * (1 / (q : ℝ)) =
        ((a : ℝ) ^ 2 + (a : ℝ) * q) / (q : ℝ) ^ 2 := by
      field_simp [hqR.ne']
    rw [he]
    apply (le_div_iff₀ (sq_pos_of_pos hqR)).mpr
    nlinarith only [hreal]

theorem unit_quadratic {a : ℕ} (ha : a ≤ 2 ^ 20) :
    (a : ℝ) ^ 2 / 4 - (21 : ℝ) / 2 * a ≤ (UnitBound a : ℝ) := by
  have hs := Finset.sum_le_sum (s := AllPrimes a) (fun q hq =>
    twice_weight_bound a (Finset.mem_filter.mp hq).2.pos)
  have hs' : 2 * ((∑ q ∈ AllPrimes a, Weight a q : ℕ) : ℝ) ≤
      (a : ℝ) ^ 2 * (∑ q ∈ AllPrimes a, (1 : ℝ) / (q : ℝ) ^ 2) +
        (a : ℝ) * (∑ q ∈ AllPrimes a, (1 : ℝ) / (q : ℝ)) := by
    simpa only [Nat.cast_sum, Finset.mul_sum, Finset.sum_add_distrib] using hs
  have hsq := mul_le_mul_of_nonneg_left (prime_square_sum a) (sq_nonneg (a : ℝ))
  have hrec := mul_le_mul_of_nonneg_left (prime_reciprocal ha) (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  norm_num only [Nat.cast_ofNat] at hrec
  have hnat : a.choose 2 ≤ UnitBound a + ∑ q ∈ AllPrimes a, Weight a q := by unfold UnitBound; omega
  have hnatR : (a.choose 2 : ℝ) ≤ (UnitBound a : ℝ) + ((∑ q ∈ AllPrimes a, Weight a q : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hchoose : 2 * (a.choose 2 : ℝ) + (a : ℝ) = (a : ℝ) * a := by exact_mod_cast choose_two_twice a
  nlinarith only [hs', hsq, hrec, hnatR, hchoose]

theorem unit_tail84 {a : ℕ} (hlo : 84 ≤ a) (hhi : a ≤ 2 ^ 20) :
    (a : ℝ) ^ 2 / 8 - 1 ≤ (UnitBound a : ℝ) := by
  have hq := unit_quadratic hhi
  have hloR : (84 : ℝ) ≤ a := by exact_mod_cast hlo
  have hn : 0 ≤ (a : ℝ) * ((a : ℝ) - 84) := mul_nonneg (Nat.cast_nonneg a) (sub_nonneg.mpr hloR)
  nlinarith only [hq, hn]

#print axioms all_primes_subset_odd
#print axioms prime_square_sum
#print axioms twice_weight_bound
#print axioms unit_quadratic
#print axioms unit_tail84
end
end JSP233.PrimeQuadratic200000
