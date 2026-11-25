module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace JSP233.IntegerFee65968
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Upper (x K q : ℝ) (a b c : ℤ) : ℝ :=
  x^2*(a : ℝ)/K+q*x+(c : ℝ)+x*((b : ℝ)/K)

theorem integer_coefficients {ι : Type*} (I : Finset ι)
    (δ a b c : ι → ℤ) (x K q : ℝ) :
    (∑ i ∈ I, (δ i : ℝ)*Upper x K q (a i) (b i) (c i)) =
      ((∑ i ∈ I, δ i*a i : ℤ) : ℝ)/K*x^2+
      (q*((∑ i ∈ I, δ i : ℤ) : ℝ)+
        ((∑ i ∈ I, δ i*b i : ℤ) : ℝ)/K)*x+
      ((∑ i ∈ I, δ i*c i : ℤ) : ℝ) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Int.cast_add]
    rw [ih]
    simp only [Upper, Int.cast_mul]
    ring

#print axioms integer_coefficients
end
end JSP233.IntegerFee65968
