module

public import Mathlib.Data.Nat.Totient
public import Erdos272.Foundation.ProofTactics

@[expose] public section

/-! # Kernel-checkable totient tables

A proposed table is certified by its divisor sums, using the mathematical
uniqueness of the Euler totient recurrence.  In particular, neither a digest
nor the return value of a native executable is a premise of the theorem.
-/
namespace JSP233.TotientTable208
open scoped BigOperators

/-- A table satisfying the defining divisor-sum identities agrees with
`Nat.totient` throughout the claimed finite range. -/
theorem correct_of_divisor_sums (a : ℕ → ℕ) (H : ℕ) (hz : a 0 = 0)
    (hs : ∀ n, 0 < n → n ≤ H → ∑ d ∈ n.divisors, a d = n) :
    ∀ n, n ≤ H → a n = Nat.totient n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnH
    by_cases hn : n = 0
    · simpa [hn] using hz
    have hn0 : 0 < n := by omega
    have hmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, hn⟩
    have hproper : (∑ d ∈ n.divisors.erase n, a d) =
        ∑ d ∈ n.divisors.erase n, Nat.totient d := by
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨hdn, hdiv⟩ := Finset.mem_erase.mp hd
      have hdle : d ≤ n := Nat.le_of_dvd hn0 (Nat.dvd_of_mem_divisors hdiv)
      exact ih d (by omega) (hdle.trans hnH)
    have ha := hs n hn0 hnH
    have hp := Nat.sum_totient n
    rw [← Finset.sum_erase_add _ _ hmem] at ha hp
    omega

/-- This check is intended for a computable lookup function supplied by a
generated Lean data file.  Soundness is independent of that generator. -/
def check (a : ℕ → ℕ) (H : ℕ) : Bool :=
  decide (a 0 = 0) &&
    ((List.range H).all fun j => decide (∑ d ∈ (j + 1).divisors, a d = j + 1))

theorem check_sound {a : ℕ → ℕ} {H : ℕ} (hc : check a H = true) :
    ∀ n, n ≤ H → a n = Nat.totient n := by
  have hpair : decide (a 0 = 0) = true ∧
      (List.range H).all (fun j => decide (∑ d ∈ (j + 1).divisors, a d = j + 1)) = true := by
    simpa only [check, Bool.and_eq_true_iff] using hc
  obtain ⟨hz, hs⟩ := hpair
  apply correct_of_divisor_sums a H (of_decide_eq_true hz)
  intro n hn hnH
  have hj : n - 1 ∈ List.range H := by
    simp only [List.mem_range]
    omega
  have hh := of_decide_eq_true ((List.all_eq_true.mp hs) (n - 1) hj)
  simpa only [Nat.sub_add_cancel hn] using hh

#print axioms correct_of_divisor_sums
#print axioms check_sound
end JSP233.TotientTable208
