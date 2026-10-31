import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-! # Kernel certification of a totient sieve by prime recurrences

The proposed factor in each row must be prime, divide the row index, and
leave a strictly smaller quotient. The totient recurrence then proves the
lookup correct by strong induction. No property of the generator is trusted.
-/
namespace JSP233.TotientSieve208

def Step (a factor : ℕ → ℕ) (n : ℕ) : Prop :=
  let p := factor n
  let m := n / p
  p.Prime ∧ n = p * m ∧ m < n ∧
    a n = (if p ∣ m then p else p - 1) * a m

instance (a factor : ℕ → ℕ) (n : ℕ) : Decidable (Step a factor n) := by
  unfold Step
  infer_instance

theorem correct_of_steps (a factor : ℕ → ℕ) (H : ℕ)
    (hz : a 0 = 0) (ho : a 1 = 1)
    (hs : ∀ n, 2 ≤ n → n ≤ H → Step a factor n) :
    ∀ n, n ≤ H → a n = Nat.totient n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnH
    by_cases hn0 : n = 0
    · simpa only [hn0, Nat.totient_zero] using hz
    by_cases hn1 : n = 1
    · simpa only [hn1, Nat.totient_one] using ho
    have hn2 : 2 ≤ n := by omega
    obtain ⟨hp, heq, hmn, hr⟩ := hs n hn2 hnH
    have hmH : n / factor n ≤ H := hmn.le.trans hnH
    have hm := ih (n / factor n) hmn hmH
    have hprod : Nat.totient n =
        (if factor n ∣ n / factor n then factor n else factor n - 1) *
          Nat.totient (n / factor n) := by
      conv_lhs => rw [heq]
      split_ifs with hd
      · exact Nat.totient_mul_of_prime_of_dvd hp hd
      · exact Nat.totient_mul_of_prime_of_not_dvd hp hd
    rw [hprod, ← hm]
    exact hr

def checkStep (a factor : ℕ → ℕ) (n : ℕ) : Bool := decide (Step a factor n)

def check (a factor : ℕ → ℕ) (H : ℕ) : Bool :=
  decide (a 0 = 0 ∧ a 1 = 1) &&
    (List.range (H - 1)).all (fun j => checkStep a factor (j + 2))

theorem check_sound {a factor : ℕ → ℕ} {H : ℕ}
    (hc : check a factor H = true) :
    ∀ n, n ≤ H → a n = Nat.totient n := by
  have hp : decide (a 0 = 0 ∧ a 1 = 1) = true ∧
      (List.range (H - 1)).all (fun j => checkStep a factor (j + 2)) = true := by
    simpa only [check, Bool.and_eq_true_iff] using hc
  obtain ⟨hzero, hrows⟩ := hp
  obtain ⟨hz, ho⟩ := of_decide_eq_true hzero
  apply correct_of_steps a factor H hz ho
  intro n hn2 hnH
  have hj : n - 2 ∈ List.range (H - 1) := by
    simp only [List.mem_range]
    omega
  have hh := (List.all_eq_true.mp hrows) (n - 2) hj
  have heq : n - 2 + 2 = n := by omega
  rw [heq] at hh
  exact of_decide_eq_true hh

#print axioms correct_of_steps
#print axioms check_sound
end JSP233.TotientSieve208
