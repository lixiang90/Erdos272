module

public import Erdos272.Counting.CrossRootGap
public import Erdos272.Arithmetic.TwoSidedMoment62
public import Erdos272.Arithmetic.HarmonicSharp39
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section
namespace JSP233.CrossGap20258
open StarCompletion HarmonicAbel29 HarmonicLog55 RestrictedWitness44
open scoped Classical
noncomputable section
set_option autoImplicit false

/-- Both sides of the physical root partition the witness distances. -/
theorem exception_cap {N : ℕ} {c : ℤ} (hn : 1 ≤ N) (hi : N < 2^16)
    (hc : c ∈ Ground N) : (WitnessException (Ground N) c : ℝ) ≤ 500*N := by
  have one : (1 : ℝ) ≤ N := by exact_mod_cast hn
  have pow : (N : ℝ) ≤ (2 : ℝ)^16 := by exact_mod_cast hi.le
  have log := Real.log_le_log (by linarith only [one] : (0 : ℝ) < N) pow
  rw [Real.log_pow] at log
  have two : Real.log 2 ≤ 7/10 := Real.log_two_lt_d9.le.trans (by norm_num)
  have ell : Real.log N ≤ 56/5 := by norm_num at log; linarith only [log,two]
  have hh : Harmonic N ≤ 12 := (HarmonicSharp39.actual_harmonic_tight N 16 hi).trans (by norm_num)
  have hl := Real.log_nonneg one
  have poly : SimplexPolynomial (Real.log N) (Harmonic N) ≤ SimplexPolynomial (56/5) 12 := by
    dsimp only [SimplexPolynomial]
    gcongr
  have sc := mul_le_mul_of_nonneg_left poly (Nat.cast_nonneg (α := ℝ) N)
  norm_num [SimplexPolynomial] at sc
  have realBudget := TwoSidedMoment62.actual_simplex_exception_half hc
  dsimp only [SimplexPolynomial] at realBudget
  nlinarith only [sc,realBudget,one]

theorem actual_near_one_sided_reduction {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (lo : 19227 ≤ N) (hi : N < 2^16) (hc : c ∈ Ground N) (legal : Legal (Ground N) F)
    (root : ∀ S ∈ F, ¬IsAP S → c ∈ S) (near : 17*(N : ℝ)^2/36 < F.card) :
    Rooted F c ∨ ∃ P ∈ F, c ∉ P ∧ ((∀ x ∈ P, x < c) ∨ ∀ x ∈ P, c < x) := by
  have nlo : (19227 : ℝ) ≤ N := by exact_mod_cast lo
  exact CrossRootGap.actual_near_one_sided_reduction (e := 500) (by omega) (exception_cap (by omega) hi hc)
    ((HarmonicSharp39.actual_harmonic_tight N 16 hi).trans (by norm_num))
    (by linarith only [nlo]) (by linarith only [nlo]) hc legal root near

#print axioms exception_cap
#print axioms actual_near_one_sided_reduction
end
end JSP233.CrossGap20258
