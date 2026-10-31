import Erdos272.Arithmetic.MarkerSieve209

/-! A totient evaluator from a proposed small-factor table. The table contains
no totient values above the existing certified base. A zero factor is accepted
only when the independently checked composite cover proves primality. -/
namespace JSP233.ComputedTotient209
set_option maxHeartbeats 0

def value (base factor : Nat → Nat) (fuel n : Nat) : Nat :=
  if n ≤ 32753 then base n else
  match fuel with
  | 0 => 0
  | k + 1 =>
    let p := factor n
    if p = 0 then n - 1 else
      let m := n / p
      (if p ∣ m then p else p - 1) * value base factor k m

theorem correct {base factor : Nat → Nat} {H : Nat}
    (hbase : ∀ n, n ≤ 32753 → base n = Nat.totient n)
    (hfactor : ∀ n, 32753 < n → n ≤ H →
      (factor n = 0 → n.Prime) ∧
      (factor n ≠ 0 → (factor n).Prime ∧ factor n ∣ n))
    (fuel n : Nat) (hnH : n ≤ H) (hfuel : n < 32754 * 2^fuel) :
    value base factor fuel n = Nat.totient n := by
  induction fuel generalizing n with
  | zero =>
    have hnbase : n ≤ 32753 := by norm_num at hfuel; omega
    rw [value, if_pos hnbase, hbase n hnbase]
  | succ k ih =>
    by_cases hnbase : n ≤ 32753
    · rw [value, if_pos hnbase, hbase n hnbase]
    rw [value, if_neg hnbase]
    obtain ⟨hz, hp⟩ := hfactor n (by omega) hnH
    by_cases hp0 : factor n = 0
    · rw [if_pos hp0, Nat.totient_prime (hz hp0)]
    rw [if_neg hp0]
    obtain ⟨hpPrime, hpdvd⟩ := hp hp0
    have heq : factor n * (n / factor n) = n := Nat.mul_div_cancel' hpdvd
    have hmn : n / factor n ≤ n := Nat.div_le_self _ _
    have hmH : n / factor n ≤ H := hmn.trans hnH
    have hmfuel : n / factor n < 32754 * 2^k := by
      have hp2 := hpPrime.two_le
      rw [pow_succ] at hfuel
      by_contra h
      have hmlow : 32754 * 2^k ≤ n / factor n := by omega
      nlinarith only [heq, hp2, hmlow, hfuel]
    dsimp only
    rw [ih _ hmH hmfuel]
    conv_rhs => rw [← heq]
    split_ifs with hdiv
    · exact (Nat.totient_mul_of_prime_of_dvd hpPrime hdiv).symm
    · exact (Nat.totient_mul_of_prime_of_not_dvd hpPrime hdiv).symm

def checkFactors (factor : Nat → Nat) (isPrime : Nat → Bool) (lo len : Nat) : Bool :=
  (List.range len).all (fun j =>
    let n := lo + j
    let p := factor n
    decide (p = 0) || (isPrime p && decide (p ∣ n)))

theorem checkFactors_sound {factor : Nat → Nat} {isPrime : Nat → Bool} {lo len n : Nat}
    (hprime : ∀ p, isPrime p = true → p.Prime)
    (hc : checkFactors factor isPrime lo len = true) (hlo : lo ≤ n) (hhi : n < lo + len)
    (hp0 : factor n ≠ 0) : (factor n).Prime ∧ factor n ∣ n := by
  have hj : n - lo ∈ List.range len := by simp only [List.mem_range]; omega
  have hh := (List.all_eq_true.mp hc) (n - lo) hj
  have heq : lo + (n - lo) = n := by omega
  dsimp only at hh
  rw [heq] at hh
  have hh' : isPrime (factor n) = true ∧ decide (factor n ∣ n) = true := by
    simpa only [hp0, decide_false, Bool.false_or, Bool.and_eq_true_iff] using hh
  exact ⟨hprime _ hh'.1, of_decide_eq_true hh'.2⟩

def checkDivides (factor : Nat → Nat) (lo : Nat) : Nat → Bool
  | 0 => true
  | len + 1 =>
    let n := lo + len
    decide (factor n = 0 ∨ factor n ∣ n) && checkDivides factor lo len

theorem checkDivides_sound {factor : Nat → Nat} {lo len n : Nat}
    (hc : checkDivides factor lo len = true) (hlo : lo ≤ n) (hhi : n < lo + len)
    (hp0 : factor n ≠ 0) : factor n ∣ n := by
  induction len with
  | zero => omega
  | succ len ih =>
    obtain ⟨hh, hc'⟩ : (factor (lo + len) = 0 ∨ factor (lo + len) ∣ lo + len) ∧
        checkDivides factor lo len = true := by
      simpa only [checkDivides, Bool.and_eq_true_iff, decide_eq_true_eq] using hc
    by_cases hn : n = lo + len
    · simpa only [← hn, hp0, false_or] using hh
    · exact ih hc' (by omega)

#print axioms correct
#print axioms checkFactors_sound
#print axioms checkDivides_sound
end JSP233.ComputedTotient209
