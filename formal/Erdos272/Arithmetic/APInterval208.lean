module

public import Erdos272.Counting.ActualAPCount208
public import Erdos272.Arithmetic.PureSource208
public import Mathlib.Algebra.BigOperators.Intervals
public import Erdos272.Foundation.ProofTactics

@[expose] public section

/-! # Arithmetic conversion of the actual AP bound

The recursive geometric bound is converted into the explicit finite
integer-step sum used by the source tables.
-/
namespace JSP233.APInterval208
open ActualAPCount208 PureSource208
open scoped BigOperators

theorem choose_two_twice (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 2
  norm_num [Nat.descFactorial] at h
  by_cases hn : n = 0
  · simp [hn]
  · have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    nlinarith

/-- The doubled formula is valid at both closed boundaries. This avoids
changing a quotient when a remainder reaches the next shorter AP length. -/
theorem bound_window (q : ℕ) (hq : 1 ≤ q) (n D : ℕ)
    (hl : q * D ≤ n) (hu : n ≤ q * (D + 1)) :
    2 * Bound n q + q * D * (D + 1) = 2 * D * n := by
  induction q using Nat.strong_induction_on generalizing n D with
  | h q ih =>
    match q with
    | 0 => omega
    | 1 =>
      have hc := choose_two_twice n
      simp only [Bound, one_mul] at hl hu ⊢
      have hcases : n = D ∨ n = D + 1 := by omega
      rcases hcases with rfl | rfl <;> nlinarith
    | r + 2 =>
      let Q := r + 2
      let E := n / Q
      let m := n - E
      have hQ : 0 < Q := by dsimp [Q]; omega
      have hE : E ≤ n := Nat.div_le_self _ _
      have hm : m + E = n := Nat.sub_add_cancel hE
      have hEn : Q * E ≤ n := Nat.mul_div_le n Q
      have hEn' : n < Q * (E + 1) := Nat.lt_mul_div_succ n hQ
      have hmlo : (r + 1) * E ≤ m := by dsimp [Q] at hEn; nlinarith
      have hmhi : m ≤ (r + 1) * (E + 1) := by
        dsimp [Q] at hEn'
        nlinarith
      have hp := ih (r + 1) (by omega) (by omega) m E hmlo hmhi
      have hc := choose_two_twice E
      have hmE := congrArg (fun z : ℕ => 2 * E * z) hm
      have heq : 2 * Bound n (r + 2) + Q * E * (E + 1) = 2 * E * n := by
        change 2 * (Bound m (r + 1) + E.choose 2) + Q * E * (E + 1) = 2 * E * n
        dsimp only [Q]
        nlinarith only [hp, hc, hmE]
      have hDE : D ≤ E := by
        by_contra h
        have hlt : E + 1 ≤ D := by omega
        have hmul := Nat.mul_le_mul_left Q hlt
        change Q * D ≤ n at hl
        omega
      have hED : E ≤ D + 1 := by
        by_contra h
        have hlt : D + 2 ≤ E := by omega
        have hmul := Nat.mul_le_mul_left Q hlt
        change n ≤ Q * (D + 1) at hu
        nlinarith
      have hcases : E = D ∨ E = D + 1 := by omega
      rcases hcases with hsame | hnext
      · simpa only [hsame] using heq
      · have hn : n = Q * (D + 1) := by
          change n ≤ Q * (D + 1) at hu
          rw [hnext] at hEn
          omega
        rw [hnext, hn] at heq
        change 2 * Bound n (r + 2) + Q * D * (D + 1) = 2 * D * n
        rw [hn]
        nlinarith only [heq]

theorem sum_Icc_twice (D : ℕ) :
    2 * (∑ d ∈ Finset.Icc 1 D, d) = D * (D + 1) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    nlinarith only [ih]

theorem intervalMultiplicity_truncate {q n D : ℕ} (hq : 1 ≤ q)
    (hl : q * D ≤ n) (hu : n ≤ q * (D + 1)) :
    intervalMultiplicity n q = ∑ d ∈ Finset.Icc 1 D, (n - d * q) := by
  have hDn : D ≤ n := by nlinarith
  have hsub : Finset.Icc 1 D ⊆ Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans hDn⟩
  unfold intervalMultiplicity
  symm
  apply Finset.sum_subset hsub
  intro d hd hnot
  have hd1 := (Finset.mem_Icc.mp hd).1
  have hDd : D + 1 ≤ d := by
    by_contra h
    exact hnot (Finset.mem_Icc.mpr ⟨hd1, by omega⟩)
  have hn : n ≤ d * q := by nlinarith
  exact Nat.sub_eq_zero_of_le hn

theorem interval_window {q n D : ℕ} (hq : 1 ≤ q)
    (hl : q * D ≤ n) (hu : n ≤ q * (D + 1)) :
    2 * intervalMultiplicity n q + q * D * (D + 1) = 2 * D * n := by
  rw [intervalMultiplicity_truncate hq hl hu]
  have hs : (∑ d ∈ Finset.Icc 1 D, (n - d * q)) +
      (∑ d ∈ Finset.Icc 1 D, d * q) = D * n := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ d ∈ Finset.Icc 1 D, (n - d * q + d * q)) =
          ∑ _d ∈ Finset.Icc 1 D, n := by
        apply Finset.sum_congr rfl
        intro d hd
        apply Nat.sub_add_cancel
        have hdD := (Finset.mem_Icc.mp hd).2
        nlinarith
      _ = D * n := by simp
  rw [← Finset.sum_mul] at hs
  have hD := congrArg (fun z : ℕ => q * z) (sum_Icc_twice D)
  nlinarith only [hs, hD]

/-- The integer-interval step formula is the exact value of the recursive
geometric bound, for every finite source size and every AP length. -/
theorem bound_eq_intervalMultiplicity {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    Bound n q = intervalMultiplicity n q := by
  let D := n / q
  have hl : q * D ≤ n := Nat.mul_div_le n q
  have hu : n ≤ q * (D + 1) := (Nat.lt_mul_div_succ n (by omega)).le
  have hb := bound_window q hq n D hl hu
  have hi := interval_window hq hl hu
  omega

/-- Every actual integer set has at most as many positive-step APs of the
specified length as a dense interval with the same cardinality. -/
theorem actual_AP_count_le_interval {q : ℕ} (hq : 1 ≤ q) (S : Finset ℤ) :
    (Codes S q).card ≤ intervalMultiplicity S.card q := by
  rw [← bound_eq_intervalMultiplicity hq]
  exact count_le_bound q hq S

#print axioms choose_two_twice
#print axioms bound_window
#print axioms interval_window
#print axioms bound_eq_intervalMultiplicity
#print axioms actual_AP_count_le_interval
end JSP233.APInterval208
