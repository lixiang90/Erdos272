module

public import Erdos272.Arithmetic.ResidueSource208
public import Erdos272.Arithmetic.FastSource208
public import Erdos272.Arithmetic.TotientTail208
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.SourceMoment291012
open PureSource208 ResidueSource208
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Prefix (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ q ∈ Finset.range n, a q

def Moment (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ q ∈ Finset.range n, q * a q

def Value (p q : ℕ → ℕ) (s e : ℕ) : ℕ :=
  s * (p s - p (s-e)) - (q s - q (s-e))

theorem prefix_difference (a : ℕ → ℕ) {lo hi : ℕ} (h : lo ≤ hi) :
    Prefix a hi - Prefix a lo = ∑ q ∈ Finset.Ico lo hi, a q := by
  have hs := Finset.sum_range_add_sum_Ico a h
  change Prefix a lo + (∑ q ∈ Finset.Ico lo hi, a q) = Prefix a hi at hs
  omega

theorem value_eq_d1 (a : ℕ → ℕ) (s e : ℕ) :
    Value (Prefix a) (Moment a) s e =
      ∑ q ∈ Finset.Ico (s-e) s, a q * (s-q) := by
  have hp := prefix_difference a (Nat.sub_le s e)
  have hq := prefix_difference (fun q => q * a q) (Nat.sub_le s e)
  change Moment a s - Moment a (s-e) = _ at hq
  unfold Value
  rw [hp, hq, Finset.mul_sum]
  have hpoint : (∑ q ∈ Finset.Ico (s-e) s, s * a q) =
      (∑ q ∈ Finset.Ico (s-e) s, a q * (s-q)) +
      ∑ q ∈ Finset.Ico (s-e) s, q * a q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hqs := (Finset.mem_Ico.mp hq).2.le
    have hh := Nat.sub_add_cancel hqs
    nlinarith only [hh]
  omega

theorem value_lower {s e : ℕ} (he : e ≤ s) :
    Value (Prefix Nat.totient) (Moment Nat.totient) s e ≤ physicalK s e := by
  rw [value_eq_d1]
  rw [← reverse_weighted_sum s e he Nat.totient]
  exact actual_d1_source_lower he

#print axioms prefix_difference
#print axioms value_eq_d1
#print axioms value_lower
end JSP233.SourceMoment291012
