import Erdos272.Arithmetic.TotientSieve208

/-! A kernel-computable prime test for the totient recurrence checker.
The ordinary `Decidable Nat.Prime` instance checks all smaller candidates.
This checker stops at the integer square root, with a mathematical soundness
proof.  The generic interface also accepts independently proved prime tables.
-/
namespace JSP233.TotientSieveFast208
set_option maxHeartbeats 0

def primeCheck (n : ℕ) : Bool :=
  decide (2 ≤ n) &&
    (List.range (Nat.sqrt n - 1)).all (fun j => decide (¬ j + 2 ∣ n))

theorem primeCheck_sound {n : ℕ} (hc : primeCheck n = true) : n.Prime := by
  have hp : decide (2 ≤ n) = true ∧
      (List.range (Nat.sqrt n - 1)).all (fun j => decide (¬ j + 2 ∣ n)) = true := by
    simpa only [primeCheck, Bool.and_eq_true_iff] using hc
  refine Nat.prime_def_le_sqrt.mpr ⟨of_decide_eq_true hp.1, ?_⟩
  intro m hm2 hmsqrt
  have hj : m - 2 ∈ List.range (Nat.sqrt n - 1) := by
    simp only [List.mem_range]
    omega
  have hh := (List.all_eq_true.mp hp.2) (m - 2) hj
  have heq : m - 2 + 2 = m := by omega
  rw [heq] at hh
  exact of_decide_eq_true hh

theorem primeCheck_complete {n : ℕ} (hp : n.Prime) : primeCheck n = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact decide_eq_true hp.two_le
  · apply List.all_eq_true.mpr
    intro j hj
    have hjlt : j < Nat.sqrt n - 1 := List.mem_range.mp hj
    have hj2 : 2 ≤ j + 2 := by omega
    have hjsqrt : j + 2 ≤ Nat.sqrt n := by omega
    exact decide_eq_true ((Nat.prime_def_le_sqrt.mp hp).2 _ hj2 hjsqrt)

def checkStepWith (isPrime : ℕ → Bool) (a factor : ℕ → ℕ) (n : ℕ) : Bool :=
  isPrime (factor n) &&
    decide (n = factor n * (n / factor n) ∧ n / factor n < n ∧
      a n = (if factor n ∣ n / factor n then factor n else factor n - 1) * a (n / factor n))

def checkWith (isPrime : ℕ → Bool) (a factor : ℕ → ℕ) (H : ℕ) : Bool :=
  decide (a 0 = 0 ∧ a 1 = 1) &&
    (List.range (H - 1)).all (fun j => checkStepWith isPrime a factor (j + 2))

theorem checkStepWith_sound {isPrime : ℕ → Bool} {a factor : ℕ → ℕ} {n : ℕ}
    (hprime : ∀ p, isPrime p = true → p.Prime)
    (hc : checkStepWith isPrime a factor n = true) : TotientSieve208.Step a factor n := by
  have hh : isPrime (factor n) = true ∧
      decide (n = factor n * (n / factor n) ∧ n / factor n < n ∧
        a n = (if factor n ∣ n / factor n then factor n else factor n - 1) * a (n / factor n)) = true := by
    simpa only [checkStepWith, Bool.and_eq_true_iff] using hc
  exact ⟨hprime _ hh.1, of_decide_eq_true hh.2⟩

theorem checkWith_sound {isPrime : ℕ → Bool} {a factor : ℕ → ℕ} {H : ℕ}
    (hprime : ∀ p, isPrime p = true → p.Prime)
    (hc : checkWith isPrime a factor H = true) :
    ∀ n, n ≤ H → a n = Nat.totient n := by
  have hp : decide (a 0 = 0 ∧ a 1 = 1) = true ∧
      (List.range (H - 1)).all (fun j => checkStepWith isPrime a factor (j + 2)) = true := by
    simpa only [checkWith, Bool.and_eq_true_iff] using hc
  obtain ⟨hz, ho⟩ := of_decide_eq_true hp.1
  apply TotientSieve208.correct_of_steps a factor H hz ho
  intro n hn2 hnH
  have hj : n - 2 ∈ List.range (H - 1) := by
    simp only [List.mem_range]
    omega
  have hh := (List.all_eq_true.mp hp.2) (n - 2) hj
  have heq : n - 2 + 2 = n := by omega
  rw [heq] at hh
  exact checkStepWith_sound hprime hh

def check (a factor : ℕ → ℕ) (H : ℕ) : Bool := checkWith primeCheck a factor H

theorem check_sound {a factor : ℕ → ℕ} {H : ℕ} (hc : check a factor H = true) :
    ∀ n, n ≤ H → a n = Nat.totient n :=
  checkWith_sound (fun _ hp => primeCheck_sound hp) hc

#print axioms primeCheck_sound
#print axioms primeCheck_complete
#print axioms checkWith_sound
#print axioms check_sound
end JSP233.TotientSieveFast208
