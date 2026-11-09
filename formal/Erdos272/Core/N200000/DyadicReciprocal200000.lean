module

public import Erdos272.Core.N200000.CoreUnionSource200000
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Elementary finite reciprocal bounds for the analytic source tail.
No logarithm, zeta value, or prime-distribution estimate is required. -/
namespace JSP233.DyadicReciprocal200000
open StarCompletion APGeometry SourceBridge208 CoreUnionSource200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem reciprocal_dyadic (k : ℕ) :
    (∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ k), (1 : ℝ) / (n : ℝ)) ≤ (k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hP : 0 < (2 : ℕ) ^ k := pow_pos (by decide) k
      have htop : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      have hUnion : Finset.Ioc (1 : ℕ) (2 ^ (k + 1)) = Finset.Ioc 1 (2 ^ k) ∪ Finset.Ioc (2 ^ k) (2 ^ (k + 1)) := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_union]
        rw [htop]
        omega
      have hdis : Disjoint (Finset.Ioc (1 : ℕ) (2 ^ k)) (Finset.Ioc (2 ^ k) (2 ^ (k + 1))) := by
        apply Finset.disjoint_left.mpr
        intro n hn hm
        have hu := (Finset.mem_Ioc.mp hn).2
        have hl := (Finset.mem_Ioc.mp hm).1
        omega
      have hPR : 0 < ((2 : ℕ) ^ k : ℝ) := by exact_mod_cast hP
      have htail : (∑ n ∈ Finset.Ioc ((2 : ℕ) ^ k) (2 ^ (k + 1)), (1 : ℝ) / (n : ℝ)) ≤ 1 := by
        calc
          _ ≤ ∑ _n ∈ Finset.Ioc ((2 : ℕ) ^ k) (2 ^ (k + 1)), (1 : ℝ) / ((2 : ℕ) ^ k : ℝ) := by
            apply Finset.sum_le_sum
            intro n hn
            have hpn : 2 ^ k ≤ n := (Finset.mem_Ioc.mp hn).1.le
            exact one_div_le_one_div_of_le hPR (by exact_mod_cast hpn)
          _ = ((2 : ℕ) ^ k : ℝ) * (1 / ((2 : ℕ) ^ k : ℝ)) := by
            simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, htop, Nat.add_sub_cancel_left, Nat.cast_pow]
          _ = 1 := by simp only [one_div, mul_inv_cancel₀ hPR.ne']
      rw [hUnion, Finset.sum_union hdis]
      have hs := add_le_add ih htail
      simpa only [Nat.cast_succ] using hs

theorem prime_reciprocal {a k : ℕ} (ha : a ≤ 2 ^ k) :
    (∑ q ∈ AllPrimes a, (1 : ℝ) / (q : ℝ)) ≤ (k : ℝ) := by
  have hsub : AllPrimes a ⊆ Finset.Ioc (1 : ℕ) (2 ^ k) := by
    intro q hq
    obtain ⟨hqa, hp⟩ := Finset.mem_filter.mp hq
    have hlt := Finset.mem_range.mp hqa
    have htwo := hp.two_le
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hs : (∑ q ∈ AllPrimes a, (1 : ℝ) / (q : ℝ)) ≤
      ∑ q ∈ Finset.Ioc (1 : ℕ) (2 ^ k), (1 : ℝ) / (q : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  exact hs.trans (reciprocal_dyadic k)

theorem odd_square_step (j : ℕ) : (1 : ℝ) / (2 * (j : ℝ) + 3) ^ 2 ≤
    1 / (4 * ((j : ℝ) + 1)) - 1 / (4 * ((j : ℝ) + 2)) := by
  have h1 : 0 < (j : ℝ) + 1 := by positivity
  have h2 : 0 < (j : ℝ) + 2 := by positivity
  have he : (1 : ℝ) / (4 * ((j : ℝ) + 1)) - 1 / (4 * ((j : ℝ) + 2)) =
      1 / (4 * ((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    field_simp [h1.ne', h2.ne']
    ring
  rw [he]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem odd_square_partial (a : ℕ) : (∑ j ∈ Finset.range a, (1 : ℝ) / (2 * (j : ℝ) + 3) ^ 2) ≤
    1 / 4 - 1 / (4 * ((a : ℝ) + 1)) := by
  induction a with
  | zero => norm_num
  | succ a ih =>
      rw [Finset.sum_range_succ]
      have hs := odd_square_step a
      have hcast : ((a + 1 : ℕ) : ℝ) + 1 = (a : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      linarith only [ih, hs]

theorem odd_square_sum (a : ℕ) : (∑ j ∈ Finset.range a, (1 : ℝ) / (2 * (j : ℝ) + 3) ^ 2) ≤ 1 / 4 := by
  have hs := odd_square_partial a
  have hn : (0 : ℝ) ≤ 1 / (4 * ((a : ℝ) + 1)) := by positivity
  linarith only [hs, hn]

#print axioms reciprocal_dyadic
#print axioms prime_reciprocal
#print axioms odd_square_step
#print axioms odd_square_partial
#print axioms odd_square_sum
end
end JSP233.DyadicReciprocal200000
