import Erdos272.Arithmetic.APInterval208
import Erdos272.Arithmetic.TotientTable208
import Mathlib.Tactic

/-! # Efficient kernel evaluation of the exact physical source

The positive-part step sum is replaced by its proved quadratic expression.
A proposed totient lookup is used only after its correctness is proved.
This module contains no numerical source table.
-/
namespace JSP233.FastSource208
open PureSource208 APInterval208
open scoped BigOperators

def fastMultiplicity (s q : ℕ) : ℕ :=
  if q = 0 then s * s else
    (2 * (s / q) * s - q * (s / q) * (s / q + 1)) / 2

theorem fastMultiplicity_eq (s q : ℕ) :
    fastMultiplicity s q = intervalMultiplicity s q := by
  by_cases hq : q = 0
  · subst q
    simp [fastMultiplicity, intervalMultiplicity]
  · let D := s / q
    have hl : q * D ≤ s := Nat.mul_div_le s q
    have hu : s ≤ q * (D + 1) := (Nat.lt_mul_div_succ s (by omega)).le
    have hi := interval_window (by omega : 1 ≤ q) hl hu
    have he : 2 * D * s - q * D * (D + 1) = 2 * intervalMultiplicity s q := by
      omega
    simp only [fastMultiplicity, if_neg hq]
    change (2 * D * s - q * D * (D + 1)) / 2 = intervalMultiplicity s q
    rw [he]
    omega

def fastPhysicalK (a : ℕ → ℕ) (s e : ℕ) : ℕ :=
  ∑ q ∈ Finset.Ico (s - e) s, a q * fastMultiplicity s q

theorem fastPhysicalK_eq {a : ℕ → ℕ} {H s : ℕ}
    (ha : ∀ q, q ≤ H → a q = Nat.totient q) (hs : s ≤ H) (e : ℕ) :
    fastPhysicalK a s e = physicalK s e := by
  apply Finset.sum_congr rfl
  intro q hq
  have hqs : q < s := (Finset.mem_Ico.mp hq).2
  rw [ha q (hqs.le.trans hs), fastMultiplicity_eq]

def checkFloorFast (a : ℕ → ℕ) (T H e b : ℕ) : Bool :=
  (List.range (H + 1 - T)).all fun j => decide (b ≤ fastPhysicalK a (T + j) e)

theorem checkFloorFast_sound {a : ℕ → ℕ} {T H e b : ℕ}
    (ha : ∀ q, q ≤ H → a q = Nat.totient q) (hTH : T ≤ H)
    (hc : checkFloorFast a T H e b = true) :
    b ≤ finiteMinimum T H e hTH := by
  apply (le_finiteMinimum_iff hTH).mpr
  intro s hTs hsH
  have hj : s - T ∈ List.range (H + 1 - T) := by
    simp only [List.mem_range]
    omega
  have hh := (List.all_eq_true.mp hc) (s - T) hj
  have heq : T + (s - T) = s := by omega
  have hb : b ≤ fastPhysicalK a s e := by
    simpa only [heq, decide_eq_true_eq] using hh
  rwa [fastPhysicalK_eq ha hsH e] at hb

/-- The lookup is accepted through a theorem about its exact integer
divisor identities, rather than a digest or native evaluator result. -/
theorem checked_lookup_floor {a : ℕ → ℕ} {T H e b : ℕ}
    (ha : TotientTable208.check a H = true) (hTH : T ≤ H)
    (hc : checkFloorFast a T H e b = true) :
    b ≤ finiteMinimum T H e hTH :=
  checkFloorFast_sound (TotientTable208.check_sound ha) hTH hc

#print axioms fastMultiplicity_eq
#print axioms fastPhysicalK_eq
#print axioms checkFloorFast_sound
#print axioms checked_lookup_floor
end JSP233.FastSource208
