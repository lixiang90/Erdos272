import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

namespace JSP233.SigmaSieve209
set_option maxHeartbeats 0
open Finset

/-- The physical sum of the positive divisors, with value zero at zero. -/
def sigmaOne (n : Nat) : Nat := ArithmeticFunction.sigma 1 n

theorem sigmaOne_eq_sum (n : Nat) : sigmaOne n = ∑ d ∈ n.divisors, d :=
  ArithmeticFunction.sigma_one_apply n

@[simp] theorem sigmaOne_zero : sigmaOne 0 = 0 := by simp [sigmaOne]
@[simp] theorem sigmaOne_one : sigmaOne 1 = 1 := by simp [sigmaOne]

theorem sigmaOne_prime {p : Nat} (hp : p.Prime) : sigmaOne p = p + 1 := by
  have h := @ArithmeticFunction.sigma_one_apply_prime_pow p 1 hp
  simpa [sigmaOne, Finset.sum_range_succ, Nat.add_comm] using h

theorem sigmaOne_mul_coprime {a b : Nat} (h : a.Coprime b) :
    sigmaOne (a*b) = sigmaOne a * sigmaOne b :=
  ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

def geometric (p k : Nat) : Nat := ∑ i ∈ range (k+1), p^i

theorem geometric_step (p k : Nat) :
    geometric p (k+2) + p * geometric p k = (p+1) * geometric p (k+1) := by
  have h0 : geometric p (k+1) = geometric p k + p^(k+1) := by
    simp [geometric, Finset.sum_range_succ]
  have h1 : geometric p (k+2) = geometric p (k+1) + p^(k+2) := by
    simp [geometric, Finset.sum_range_succ]
  rw [h1, h0, show p^(k+2) = p^(k+1)*p by rw [show k+2 = (k+1)+1 by omega, pow_succ]]
  ring

theorem sigmaOne_mul_prime_not_dvd {p m : Nat} (hp : p.Prime) (hm : ¬p∣m) :
    sigmaOne (p*m) = (p+1)*sigmaOne m := by
  rw [sigmaOne_mul_coprime (hp.coprime_iff_not_dvd.mpr hm), sigmaOne_prime hp]

theorem sigmaOne_mul_prime_dvd {p m : Nat} (hp : p.Prime) (hm0 : m≠0) (hm : p∣m) :
    sigmaOne (p*m) + p*sigmaOne (m/p) = (p+1)*sigmaOne m := by
  obtain ⟨k, a, ha, hma⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
  have hka : k≠0 := by
    intro hk
    rw [hk, pow_zero, one_mul] at hma
    exact ha (hma ▸ hm)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hka
  have hc : p.Coprime a := hp.coprime_iff_not_dvd.mpr ha
  have hmdiv : m/p = p^j*a := by
    rw [hma, pow_succ']
    simpa [mul_assoc] using Nat.mul_div_cancel_left (p^j*a) hp.pos
  have hpm : p*m = p^(j+2)*a := by simp only [hma, show j+2 = j.succ+1 by omega, pow_succ', mul_assoc]
  rw [hpm, hmdiv, hma, sigmaOne_mul_coprime (hc.pow_left _),
    sigmaOne_mul_coprime (hc.pow_left _), sigmaOne_mul_coprime (hc.pow_left _)]
  simp only [sigmaOne, ArithmeticFunction.sigma_one_apply_prime_pow hp]
  change geometric p (j+2)*sigmaOne a + p*(geometric p j*sigmaOne a) =
    (p+1)*(geometric p (j+1)*sigmaOne a)
  nlinarith only [geometric_step p j]

/-- A local arithmetic row. The nonzero marker is the proposed prime factor. -/
def Step (a factor : Nat→Nat) (n : Nat) : Prop :=
  let p := factor n
  if p=0 then a n=n+1 else
    let m := n/p
    if p∣m then a n+p*a (m/p)=(p+1)*a m else a n=(p+1)*a m

instance (a factor : Nat→Nat) (n : Nat) : Decidable (Step a factor n) :=
  inferInstanceAs (Decidable (let p := factor n; if p=0 then a n=n+1 else
    let m := n/p; if p∣m then a n+p*a (m/p)=(p+1)*a m else a n=(p+1)*a m))

theorem correct {a factor : Nat→Nat} {H : Nat}
    (ha0 : a 0=0) (ha1 : a 1=1)
    (hfactor : ∀ n, 2≤n → n≤H →
      (factor n=0 → n.Prime) ∧
      (factor n≠0 → (factor n).Prime ∧ factor n∣n))
    (hstep : ∀ n, 2≤n → n≤H → Step a factor n)
    (n : Nat) (hnH : n≤H) : a n=sigmaOne n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n=0
    · subst n; simpa using ha0
    by_cases hn1 : n=1
    · subst n; simpa using ha1
    have hn2 : 2≤n := by omega
    obtain ⟨hz,hp⟩ := hfactor n hn2 hnH
    have hs := hstep n hn2 hnH
    unfold Step at hs
    by_cases hp0 : factor n=0
    · rw [if_pos hp0] at hs
      rw [hs, sigmaOne_prime (hz hp0)]
    rw [if_neg hp0] at hs
    obtain ⟨hpprime,hpdvd⟩ := hp hp0
    have heq : factor n*(n/factor n)=n := Nat.mul_div_cancel' hpdvd
    have hm : n/factor n<n := Nat.div_lt_self (by omega) hpprime.one_lt
    have hm0 : n/factor n≠0 := by intro hh; rw [hh,mul_zero] at heq; omega
    have hmH : n/factor n≤H := (Nat.le_of_lt hm).trans hnH
    have ham := ih _ hm hmH
    have hamm := ih (n/factor n/factor n)
      (lt_of_le_of_lt (Nat.div_le_self _ _) hm)
      ((Nat.div_le_self _ _).trans hmH)
    dsimp only at hs
    split_ifs at hs with hdiv
    · rw [ham,hamm] at hs
      have hmrec := sigmaOne_mul_prime_dvd hpprime hm0 hdiv
      rw [heq] at hmrec
      omega
    · rw [ham] at hs
      have hh := sigmaOne_mul_prime_not_dvd hpprime hdiv
      rw [heq] at hh
      rw [hh]
      exact hs

#print axioms sigmaOne_mul_prime_dvd
#print axioms correct
end JSP233.SigmaSieve209



