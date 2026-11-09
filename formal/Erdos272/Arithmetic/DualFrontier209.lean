module

public import Erdos272.Arithmetic.FrontierCheck209
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace JSP233.DualFrontier209
open scoped BigOperators
set_option maxHeartbeats 0

def UpperGood (t f : Nat) : Prop :=
  1000 * (f + t) ≤ FrontierCheck209.Grid * (608 * t + 579)
instance (t f : Nat) : Decidable (UpperGood t f) := by unfold UpperGood; infer_instance
def Good (t f u : Nat) : Prop := FrontierCheck209.Good t f u ∧ UpperGood t f
instance (t f u : Nat) : Decidable (Good t f u) := by unfold Good; infer_instance

def checkFrom (a : Nat → Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | _, 0, f, u, fEnd, uEnd => decide (f = fEnd ∧ u = uEnd)
  | n, k + 1, f, u, fEnd, uEnd =>
    let t := n + 1
    let f' := f + FrontierCheck209.Grid * a t / t
    let u' := u + if t = 1 then 0 else a t
    decide (Good t f' u') && checkFrom a t k f' u' fEnd uEnd

theorem checkFrom_sound (a : Nat → Nat) (k n f u fEnd uEnd : Nat)
    (hf : f = FrontierCheck209.massFloor a n) (hu : u = FrontierCheck209.triangle a n)
    (hc : checkFrom a n k f u fEnd uEnd = true) :
    (fEnd = FrontierCheck209.massFloor a (n + k) ∧ uEnd = FrontierCheck209.triangle a (n + k)) ∧
    ∀ t, n < t → t ≤ n + k → Good t
      (FrontierCheck209.massFloor a t) (FrontierCheck209.triangle a t) := by
  induction k generalizing n f u with
  | zero =>
    have he : f = fEnd ∧ u = uEnd := of_decide_eq_true hc
    constructor
    · simpa only [Nat.add_zero] using ⟨he.1.symm.trans hf, he.2.symm.trans hu⟩
    · intro t ht ht'; omega
  | succ k ih =>
    have hp : Good (n + 1) (f + FrontierCheck209.Grid * a (n + 1) / (n + 1))
        (u + if n + 1 = 1 then 0 else a (n + 1)) ∧
        checkFrom a (n + 1) k (f + FrontierCheck209.Grid * a (n + 1) / (n + 1))
          (u + if n + 1 = 1 then 0 else a (n + 1)) fEnd uEnd = true := by
      simpa only [checkFrom, Bool.and_eq_true_iff, decide_eq_true_eq] using hc
    have hf' : f + FrontierCheck209.Grid * a (n + 1) / (n + 1) = FrontierCheck209.massFloor a (n + 1) := by rw [hf]; rfl
    have hu' : (u + if n + 1 = 1 then 0 else a (n + 1)) = FrontierCheck209.triangle a (n + 1) := by rw [hu]; rfl
    have hh := ih (n + 1) _ _ hf' hu' hp.2
    constructor
    · have heq : n + 1 + k = n + (k + 1) := by omega
      simpa only [heq] using hh.1
    · intro t hnt hthi
      by_cases ht : t = n + 1
      · subst t
        simpa only [hf', hu'] using hp.1
      · apply hh.2 t (by omega); omega

theorem mass_le_cast_floor (a : Nat → Nat) (t : Nat) :
    FrontierCheck209.Grid * (∑ n ∈ Finset.Icc 1 t, (a n : Real) / n) ≤
      FrontierCheck209.massFloor a t + t := by
  rw [FrontierCheck209.massFloor_eq_sum, Nat.cast_sum, Finset.mul_sum]
  have hsum : (∑ n ∈ Finset.Icc 1 t, (FrontierCheck209.Grid : Real) * ((a n : Real) / n)) ≤
      ∑ n ∈ Finset.Icc 1 t, (((FrontierCheck209.Grid * a n / n : Nat) : Real) + 1) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnpos : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
    let x := FrontierCheck209.Grid * a n
    have hmod := Nat.mod_lt x hnpos
    have hdiv := Nat.mod_add_div x n
    have hm : x ≤ (x / n + 1) * n := by nlinarith only [hmod, hdiv]
    have hm' : (FrontierCheck209.Grid : Real) * a n ≤
        (((FrontierCheck209.Grid * a n / n : Nat) : Real) + 1) * n := by exact_mod_cast hm
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (by exact_mod_cast hnpos : (0 : Real) < n)).mpr hm'
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, mul_one] using hsum

theorem actual_upper {a : Nat → Nat} {t : Nat}
    (ha : ∀ n, n ≤ t → a n = Nat.totient n)
    (hu : UpperGood t (FrontierCheck209.massFloor a t)) :
    (∑ n ∈ Finset.Icc 1 t, (Nat.totient n : Real) / n) ≤
      (76 / 125 : Real) * t + 579 / 1000 := by
  have hs := mass_le_cast_floor a t
  have heq : (∑ n ∈ Finset.Icc 1 t, (a n : Real) / n) =
      ∑ n ∈ Finset.Icc 1 t, (Nat.totient n : Real) / n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ha n (Finset.mem_Icc.mp hn).2]
  rw [heq] at hs
  have hu' : (1000 : Real) * (FrontierCheck209.massFloor a t + t) ≤
      (FrontierCheck209.Grid : Real) * (608 * t + 579) := by exact_mod_cast hu
  norm_num only [FrontierCheck209.Grid, Nat.cast_ofNat] at hs hu'
  nlinarith only [hs, hu']

#print axioms checkFrom_sound
#print axioms actual_upper
end JSP233.DualFrontier209
