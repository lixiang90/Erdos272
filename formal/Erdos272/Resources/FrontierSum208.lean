module

public import Erdos272.Resources.LocalizedMiddle208
public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! The complete local frontier price, including the truncated main tail. -/
namespace JSP233.FrontierSum208
open HarmonicAbel29 SimplexMoment57
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Polynomial (t : ℝ) : ℝ := t^2/4+(289/100)*t+12060409/4000000

def Error (L d : ℕ) : ℝ :=
  ((2 : ℝ)+39/100)*L/d + (329/200 : ℝ)*(39/100)^2/2 +
    ((L : ℝ)/(2*d))*Real.log ((L : ℝ)/d)

theorem row_error_physical {c L d : ℕ} (hcL : c ≤ L) (hd : d ∈ Finset.Icc 1 L) :
    ((c/d : ℕ) : ℝ)/2*Real.log (c/d : ℕ) ≤
      ((L : ℝ)/(2*d))*Real.log ((L : ℝ)/d) := by
  obtain ⟨hdpos, hdL⟩ := Finset.mem_Icc.mp hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hLd : (1 : ℝ) ≤ (L : ℝ)/d := (le_div_iff₀ hdR).mpr (by simpa using (show (d : ℝ) ≤ L by exact_mod_cast hdL))
  have hlog : 0 ≤ Real.log ((L : ℝ)/d) := Real.log_nonneg hLd
  by_cases hc0 : c/d = 0
  · rw [hc0]
    norm_num
    positivity
  · have hC1 : (1 : ℝ) ≤ (c/d : ℕ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hc0)
    have hCpos : (0 : ℝ) < (c/d : ℕ) := by linarith only [hC1]
    have hC : ((c/d : ℕ) : ℝ) ≤ (L : ℝ)/d :=
      (Nat.cast_div_le (α := ℝ) (m := c) (n := d)).trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hcL) hdR.le)
    have hlogs := Real.log_le_log hCpos hC
    have hlogC := Real.log_nonneg hC1
    have hh := mul_le_mul (div_le_div_of_nonneg_right hC (by norm_num : (0 : ℝ) ≤ 2))
      hlogs hlogC (by positivity : (0 : ℝ) ≤ (L : ℝ)/d/2)
    have heq : (L : ℝ)/(2*d) = (L : ℝ)/d/2 := by ring
    rw [heq]
    exact hh

theorem error_sum_identity {L : ℕ} (hL : 1 ≤ L) :
    (∑ d ∈ Finset.Icc 1 L, Error L d) =
      ((2 : ℝ)+39/100)*L*Harmonic L +
      (329/200 : ℝ)*(39/100)^2/2*L +
      ((L : ℝ)/2)*(∑ d ∈ Finset.Icc 1 L, LogKernel L 1 d) := by
  have hterms : ∀ d ∈ Finset.Icc 1 L, Error L d =
      ((2 : ℝ)+39/100)*L*(1/d) + (329/200 : ℝ)*(39/100)^2/2 +
      ((L : ℝ)/2)*LogKernel L 1 d := by
    intro d hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    dsimp only [Error,LogKernel]
    rw [Real.log_div hLpos.ne' hdpos.ne']
    norm_num only [pow_one]
    ring
  rw [Finset.sum_congr rfl hterms]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  dsimp only [Harmonic]
  ring

theorem complete_error_bound {L : ℕ} (hL : 1 ≤ L) :
    (∑ d ∈ Finset.Icc 1 L, Error L d) + (L : ℝ)/2 ≤
      (L : ℝ)*Polynomial (Real.log L) := by
  rw [error_sum_identity hL]
  have hh := HarmonicAbel29.harmonic_le_one_add_log L
  have hH := mul_le_mul_of_nonneg_left hh
    (show (0 : ℝ) ≤ ((2 : ℝ)+39/100)*L by positivity)
  have hk := SimplexMoment57.actual_log_kernel_sum hL 1
  norm_num only [pow_one,Nat.reduceAdd,Nat.cast_ofNat] at hk
  have hK := mul_le_mul_of_nonneg_left hk (show (0 : ℝ) ≤ (L : ℝ)/2 by positivity)
  dsimp only [Polynomial]
  nlinarith only [hH,hK]

#print axioms row_error_physical
#print axioms error_sum_identity
#print axioms complete_error_bound
end
end JSP233.FrontierSum208
