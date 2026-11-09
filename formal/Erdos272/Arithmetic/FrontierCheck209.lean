module

public import Erdos272.Arithmetic.SourceLookupFast208
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! Integer directed-rounding certificate for every finite totient prefix.
Block endpoints are part of the kernel check, so concatenating certificates
cannot silently reset either accumulated sum. -/
namespace JSP233.FrontierCheck209
open scoped BigOperators
set_option maxHeartbeats 0

def Grid : Nat := 1000000000000
def RNum : Nat := 500000000
def RDen : Nat := 822467033

def massFloor (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => massFloor a n + Grid * a (n + 1) / (n + 1)

def triangle (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => triangle a n + if n + 1 = 1 then 0 else a (n + 1)

def Good (t f u : Nat) : Prop :=
  200 * RNum * Grid * t ≤ 200 * RDen * f + 17 * RDen * Grid ∧
  100 * RNum * t^2 ≤ 200 * RDen * u + 61 * RDen * t

instance (t f u : Nat) : Decidable (Good t f u) := by unfold Good; infer_instance

def checkFrom (a : Nat → Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | _, 0, f, u, fEnd, uEnd => decide (f = fEnd ∧ u = uEnd)
  | n, k + 1, f, u, fEnd, uEnd =>
    let t := n + 1
    let f' := f + Grid * a t / t
    let u' := u + if t = 1 then 0 else a t
    decide (Good t f' u') && checkFrom a t k f' u' fEnd uEnd

theorem checkFrom_sound (a : Nat → Nat) (k n f u fEnd uEnd : Nat)
    (hf : f = massFloor a n) (hu : u = triangle a n)
    (hc : checkFrom a n k f u fEnd uEnd = true) :
    (fEnd = massFloor a (n + k) ∧ uEnd = triangle a (n + k)) ∧
    ∀ t, n < t → t ≤ n + k → Good t (massFloor a t) (triangle a t) := by
  induction k generalizing n f u with
  | zero =>
    have he : f = fEnd ∧ u = uEnd := of_decide_eq_true hc
    constructor
    · simpa only [Nat.add_zero] using ⟨he.1.symm.trans hf, he.2.symm.trans hu⟩
    · intro t ht ht'
      omega
  | succ k ih =>
    have hp : Good (n + 1) (f + Grid * a (n + 1) / (n + 1))
        (u + if n + 1 = 1 then 0 else a (n + 1)) ∧
        checkFrom a (n + 1) k (f + Grid * a (n + 1) / (n + 1))
          (u + if n + 1 = 1 then 0 else a (n + 1)) fEnd uEnd = true := by
      simpa only [checkFrom, Bool.and_eq_true_iff, decide_eq_true_eq] using hc
    have hf' : f + Grid * a (n + 1) / (n + 1) = massFloor a (n + 1) := by rw [hf]; rfl
    have hu' : (u + if n + 1 = 1 then 0 else a (n + 1)) = triangle a (n + 1) := by rw [hu]; rfl
    have hh := ih (n + 1) _ _ hf' hu' hp.2
    constructor
    · have heq : n + 1 + k = n + (k + 1) := by omega
      simpa only [heq] using hh.1
    · intro t hnt hthi
      by_cases ht : t = n + 1
      · subst t
        simpa only [hf', hu'] using hp.1
      · apply hh.2 t (by omega)
        omega

theorem massFloor_eq_sum (a : Nat → Nat) (t : Nat) :
    massFloor a t = ∑ n ∈ Finset.Icc 1 t, Grid * a n / n := by
  induction t with
  | zero => simp [massFloor]
  | succ t ih =>
    rw [massFloor, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1)]

theorem triangle_eq_sum (a : Nat → Nat) (t : Nat) :
    triangle a t = ∑ n ∈ Finset.Icc 2 t, a n := by
  induction t with
  | zero => simp [triangle]
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [triangle]
    · rw [triangle, if_neg (by omega : t + 1 ≠ 1), ih,
        Finset.sum_Icc_succ_top (by omega : 2 ≤ t + 1)]

theorem cast_massFloor_le (a : Nat → Nat) (t : Nat) :
    (massFloor a t : Real) ≤ Grid * (∑ n ∈ Finset.Icc 1 t, (a n : Real) / n) := by
  rw [massFloor_eq_sum, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
  have hnpos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : (Grid * a n / n : Nat) * n ≤ Grid * a n := Nat.div_mul_le_self _ _
  have hm' : ((Grid * a n / n : Nat) : Real) * n ≤ (Grid : Real) * a n := by exact_mod_cast hm
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hnpos).mpr hm'

theorem actual_bounds {a : Nat → Nat} {t : Nat}
    (ha : ∀ n, n ≤ t → a n = Nat.totient n)
    (hg : Good t (massFloor a t) (triangle a t)) :
    (500000000 / 822467033 : Real) * t - 17 / 200 ≤
        ∑ n ∈ Finset.Icc 1 t, (Nat.totient n : Real) / n ∧
    (500000000 / 822467033 : Real) * (t : Real)^2 / 2 - (61 / 200) * t ≤
        ((∑ n ∈ Finset.Icc 2 t, Nat.totient n : Nat) : Real) := by
  have hF := cast_massFloor_le a t
  have hF' : (massFloor a t : Real) ≤ (Grid : Real) *
      (∑ n ∈ Finset.Icc 1 t, (Nat.totient n : Real) / n) := by
    convert hF using 1
    apply congrArg ((Grid : Real) * ·)
    apply Finset.sum_congr rfl
    intro n hn
    rw [ha n (Finset.mem_Icc.mp hn).2]
  have hU : triangle a t = ∑ n ∈ Finset.Icc 2 t, Nat.totient n := by
    rw [triangle_eq_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact ha n (Finset.mem_Icc.mp hn).2
  obtain ⟨hgF, hgU⟩ := hg
  have hgF' : (200 * RNum * Grid : Real) * t ≤
      (200 * RDen : Real) * massFloor a t + (17 * RDen * Grid : Real) := by exact_mod_cast hgF
  have hgU' : (100 * RNum : Real) * (t : Real)^2 ≤
      (200 * RDen : Real) * triangle a t + (61 * RDen : Real) * t := by exact_mod_cast hgU
  rw [hU] at hgU'
  norm_num only [Grid, RNum, RDen, Nat.cast_ofNat] at hF' hgF' hgU'
  constructor <;> nlinarith only [hF', hgF', hgU']

#print axioms checkFrom_sound
#print axioms actual_bounds
end JSP233.FrontierCheck209
