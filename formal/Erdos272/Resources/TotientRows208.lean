module

public import Erdos272.Resources.ResourceSymmetry56
public import Erdos272.Arithmetic.TwoSidedMoment62
public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Actual coprime rows.  The divisor 1 has exactly zero floor error. -/
namespace JSP233.TotientRows208
open CoprimeDensity52
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Row (i e : ℕ) : Finset ℕ := (Finset.Icc 1 e).filter (i.Coprime ·)

theorem actual_row_moebius {i : ℕ} (hi : 0 < i) (e : ℕ) :
    ((Row i e).card : ℝ) = ∑ d ∈ i.divisors,
      (ArithmeticFunction.moebius d : ℝ) * (e / d : ℕ) := by
  calc
    _ = ∑ j ∈ Finset.Icc 1 e, if i.Coprime j then (1 : ℝ) else 0 := by simp [Row]
    _ = ∑ j ∈ Finset.Icc 1 e, ∑ d ∈ i.divisors,
        if d ∣ j then (ArithmeticFunction.moebius d : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (coprime_moebius_indicator hi j).symm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, card_multiples_Icc, mul_comm]

theorem signed_row_floor (e : ℕ) {d : ℕ} (hd : 0 < d) :
    (ArithmeticFunction.moebius d : ℝ) * ((e : ℝ) / d) -
      (|(ArithmeticFunction.moebius d : ℝ)| + (ArithmeticFunction.moebius d : ℝ)) / 2 +
      (if d = 1 then (1 : ℝ) else 0) ≤
      (ArithmeticFunction.moebius d : ℝ) * (e / d : ℕ) := by
  by_cases hd1 : d = 1
  · subst d
    simp
  · rw [if_neg hd1]
    have hf := TotientFloor29.nat_div_bounds e d hd
    rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;>
      rw [h] <;> norm_num <;> linarith only [hf.1, hf.2]

theorem actual_row_lower {i : ℕ} (hi : 2 ≤ i) (e : ℕ) :
    (e : ℝ) * (Nat.totient i : ℝ) / i - (i.divisors.card : ℝ) / 2 + 1 ≤
      (Row i e).card := by
  have hipos : 0 < i := by omega
  have hone : 1 ∈ i.divisors := Nat.one_mem_divisors.mpr (by omega)
  have hsumMu : (∑ d ∈ i.divisors, (ArithmeticFunction.moebius d : ℝ)) = 0 := by
    have hh := MixedFloor29.moebius_divisor_indicator i
    rw [if_neg (by omega : i ≠ 1)] at hh
    exact_mod_cast hh
  have habs : (∑ d ∈ i.divisors, |(ArithmeticFunction.moebius d : ℝ)|) ≤
      i.divisors.card := by
    calc
      _ ≤ ∑ _d ∈ i.divisors, (1 : ℝ) := Finset.sum_le_sum fun d _ =>
        TotientFloor29.moebius_abs_real_le_one d
      _ = _ := by simp
  have hsingle : (∑ d ∈ i.divisors, if d = 1 then (1 : ℝ) else 0) = 1 := by simp [hone]
  have hmain : (∑ d ∈ i.divisors,
      (ArithmeticFunction.moebius d : ℝ) * ((e : ℝ) / d)) =
      (e : ℝ) * (Nat.totient i : ℝ) / i := by
    rw [mul_div_assoc, TotientFloor29.normalized_totient_identity i hipos, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hs := Finset.sum_le_sum (s := i.divisors)
    (fun d hd => signed_row_floor e (Nat.pos_of_mem_divisors hd))
  rw [← actual_row_moebius hipos e] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  have herrEq : (∑ d ∈ i.divisors,
      (|(ArithmeticFunction.moebius d : ℝ)| + (ArithmeticFunction.moebius d : ℝ)) / 2) =
      (∑ d ∈ i.divisors, |(ArithmeticFunction.moebius d : ℝ)|) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hsumMu, add_zero]
  rw [hmain, herrEq, hsingle] at hs
  linarith only [hs, habs]

def TotientMass (C : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 C, (Nat.totient i : ℝ) / i
def RowError (C : ℕ) : ℝ := ∑ i ∈ Finset.Icc 2 C, ((i.divisors.card : ℝ) / 2 - 1)

theorem actual_rectangle_rows (C e : ℕ) :
    ((coprimeRectangle C e).card : ℝ) = ∑ i ∈ Finset.Icc 1 C, ((Row i e).card : ℝ) := by
  calc
    _ = ∑ p ∈ (Finset.Icc 1 C).product (Finset.Icc 1 e),
        if p.1.Coprime p.2 then (1 : ℝ) else 0 := by simp [coprimeRectangle]
    _ = ∑ i ∈ Finset.Icc 1 C, ∑ j ∈ Finset.Icc 1 e,
        if i.Coprime j then (1 : ℝ) else 0 := by rw [Finset.product_eq_sprod, Finset.sum_product]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Row]

theorem rectangle_row_lower (C e : ℕ) :
    (e : ℝ) * TotientMass C - RowError C ≤ (coprimeRectangle C e).card := by
  have hrow : ∀ i ∈ Finset.Icc 1 C,
      (e : ℝ) * (Nat.totient i : ℝ) / i -
        (if i = 1 then 0 else (i.divisors.card : ℝ) / 2 - 1) ≤ (Row i e).card := by
    intro i hi
    by_cases hi1 : i = 1
    · subst i
      simp [Row]
    · rw [if_neg hi1]
      have hh := actual_row_lower (i := i) (by have hh := (Finset.mem_Icc.mp hi).1; omega) e
      linarith only [hh]
  have hs := Finset.sum_le_sum hrow
  rw [Finset.sum_sub_distrib] at hs
  have hmain : (∑ i ∈ Finset.Icc 1 C, (e : ℝ) * (Nat.totient i : ℝ) / i) =
      (e : ℝ) * TotientMass C := by simp only [TotientMass, Finset.mul_sum, mul_div_assoc]
  have herr : (∑ i ∈ Finset.Icc 1 C,
      if i = 1 then (0 : ℝ) else (i.divisors.card : ℝ) / 2 - 1) = RowError C := by
    by_cases hC : C = 0
    · subst C
      norm_num [RowError]
    · have hi : Finset.Icc 1 C = insert 1 (Finset.Icc 2 C) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hi, Finset.sum_insert (by simp)]
      simp only [ite_true, zero_add, RowError]
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_neg (by have hh := (Finset.mem_Icc.mp hi).1; omega)]
  rw [hmain, herr, ← actual_rectangle_rows] at hs
  exact hs

theorem row_error_identity {C : ℕ} (hC : 1 ≤ C) :
    2 * RowError C =
      (∑ i ∈ Finset.Icc 1 C, (i.divisors.card : ℝ)) - 2 * C + 1 := by
  have hi : Finset.Icc 1 C = insert 1 (Finset.Icc 2 C) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hsum : (∑ i ∈ Finset.Icc 1 C, (i.divisors.card : ℝ)) =
      1 + ∑ i ∈ Finset.Icc 2 C, (i.divisors.card : ℝ) := by
    rw [hi, Finset.sum_insert (by simp)]
    simp
  have hcardNat : (Finset.Icc 2 C).card + 1 = C := by rw [Nat.card_Icc]; omega
  have hcard : ((Finset.Icc 2 C).card : ℝ) = (C : ℝ) - 1 := by
    have hh : ((Finset.Icc 2 C).card : ℝ) + 1 = C := by exact_mod_cast hcardNat
    linarith only [hh]
  dsimp only [RowError]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard, hsum]
  ring

theorem row_error_log (C : ℕ) : RowError C ≤ (C : ℝ) / 2 * Real.log C := by
  by_cases hC : C = 0
  · subst C
    norm_num [RowError]
  · have hC1 : 1 ≤ C := by omega
    have hid := row_error_identity hC1
    have hdiv := SimplexMoment57.actual_divisor_first_moment C
    have hh := HarmonicAbel29.harmonic_le_one_add_log C
    have hmul := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
    have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC1
    nlinarith only [hid, hdiv, hmul, hCR]

theorem rectangle_local_lower {rho eps : ℝ} {C e : ℕ}
    (hF : rho * C - eps ≤ TotientMass C) :
    rho * C * e - eps * e - (C : ℝ) / 2 * Real.log C ≤
      (coprimeRectangle C e).card := by
  have hr := rectangle_row_lower C e
  have he := mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg e : (0 : ℝ) ≤ e)
  have herr := row_error_log C
  nlinarith only [hr, he, herr]

#print axioms actual_row_moebius
#print axioms signed_row_floor
#print axioms actual_row_lower
#print axioms rectangle_row_lower
#print axioms row_error_log
#print axioms rectangle_local_lower
end
end JSP233.TotientRows208
