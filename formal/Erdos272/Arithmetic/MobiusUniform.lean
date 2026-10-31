import Erdos272.Arithmetic.Mobius1536
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Uniform finite Moebius lower bound, using the actual 1536-term certificate.
No infinite series or zeta identity is used. Floor and Abel estimates remain
outside this supplement. -/
namespace JSP233.MobiusUniform28
open scoped BigOperators
open ArithmeticFunction

noncomputable def partialSum (R : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 R, (moebius d : ℝ) / (d : ℝ)^2

theorem term_le_telescoping (n : ℕ) (hn : 1 ≤ n) :
    |(moebius (n+1) : ℝ) / ((n+1 : ℕ) : ℝ)^2| ≤
      1 / (n : ℝ) - 1 / ((n+1 : ℕ) : ℝ) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : (0 : ℝ) < n + 1 := by positivity
  have hb : |(moebius (n+1) : ℝ)| ≤ 1 := by
    exact_mod_cast (abs_moebius_le_one (n := n+1))
  rw [abs_div, abs_of_nonneg (sq_nonneg (((n+1 : ℕ) : ℝ)))]
  calc
    _ ≤ 1 / (((n+1 : ℕ) : ℝ)^2) :=
      div_le_div_of_nonneg_right hb (sq_nonneg _)
    _ ≤ 1 / (n : ℝ) - 1 / ((n+1 : ℕ) : ℝ) := by
      push_cast
      field_simp
      nlinarith

theorem partialSum_comparison (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    |partialSum n - partialSum k| ≤ 1 / (k : ℝ) - 1 / (n : ℝ) := by
  induction n, hkn using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    have hn : 1 ≤ n := hk.trans hkn
    have heq : partialSum (n+1) = partialSum n +
        (moebius (n+1) : ℝ) / ((n+1 : ℕ) : ℝ)^2 := by
      exact Finset.sum_Icc_succ_top (by omega) _
    rw [heq]
    have htriangle := abs_add_le (partialSum n - partialSum k)
      ((moebius (n+1) : ℝ) / ((n+1 : ℕ) : ℝ)^2)
    have ht := term_le_telescoping n hn
    have heq2 : partialSum n + (moebius (n+1) : ℝ) / ((n+1 : ℕ) : ℝ)^2 -
        partialSum k = (partialSum n - partialSum k) +
          (moebius (n+1) : ℝ) / ((n+1 : ℕ) : ℝ)^2 := by ring
    rw [heq2]
    linarith

theorem actual_moebius_partial_sum_lower (R : ℕ) (hR : 1 ≤ R) :
    (607 / 1000 : ℝ) - 1 / (R : ℝ) < partialSum R := by
  have hcert := MobiusCertificate28.actual_moebius_real_lower
  change (607 / 1000 : ℝ) + 1 / 1536 < partialSum 1536 at hcert
  have hp : (0 : ℝ) < R := by exact_mod_cast hR
  by_cases hsmall : R ≤ 1536
  · have hc := (abs_le.mp (partialSum_comparison R 1536 hR hsmall)).2
    norm_num at hc
    simp only [one_div] at hcert ⊢
    norm_num at hcert
    linarith
  · have hc := (abs_le.mp (partialSum_comparison 1536 R (by norm_num)
      (by omega))).1
    norm_num at hc
    have hrec : 0 < 1 / (R : ℝ) := by positivity
    simp only [one_div] at hcert hrec ⊢
    norm_num at hcert
    linarith

theorem actual_moebius_partial_sum_ge (R : ℕ) (hR : 1 ≤ R) :
    (607 / 1000 : ℝ) - 1 / (R : ℝ) ≤
      ∑ d ∈ Finset.Icc 1 R, (moebius d : ℝ) / (d : ℝ)^2 :=
  (actual_moebius_partial_sum_lower R hR).le

#print axioms term_le_telescoping
#print axioms partialSum_comparison
#print axioms actual_moebius_partial_sum_lower
#print axioms actual_moebius_partial_sum_ge
end JSP233.MobiusUniform28
