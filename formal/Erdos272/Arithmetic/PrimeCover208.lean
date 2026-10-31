import Erdos272.Arithmetic.TotientSieveFast208

/-! A bounded prime oracle for the 32753-entry SPF lookup.  The 42 small
primes and their coverage are proved by ordinary kernel-checked arithmetic.
For larger candidates, at most 42 divisibility tests are needed. -/
namespace JSP233.PrimeCover208
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def SmallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
    127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181]

theorem small_prime_sound {p : ℕ} (hp : p ∈ SmallPrimes) : p.Prime := by
  simp only [SmallPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem small_prime_cover {p : ℕ} (hp181 : p ≤ 181) (hp : p.Prime) : p ∈ SmallPrimes := by
  interval_cases p <;> norm_num [SmallPrimes] at *

def primeCheck (n : ℕ) : Bool :=
  if n ≤ 181 then decide (n ∈ SmallPrimes)
  else decide (n < 182 * 182) && SmallPrimes.all (fun p => decide (¬ p ∣ n))

theorem primeCheck_sound {n : ℕ} (hc : primeCheck n = true) : n.Prime := by
  by_cases hn : n ≤ 181
  · have hmem : decide (n ∈ SmallPrimes) = true := by
      simpa only [primeCheck, if_pos hn] using hc
    exact small_prime_sound (of_decide_eq_true hmem)
  · have hh : decide (n < 182 * 182) = true ∧
        SmallPrimes.all (fun p => decide (¬ p ∣ n)) = true := by
      simpa only [primeCheck, if_neg hn, Bool.and_eq_true_iff] using hc
    have hbound : n < 182 * 182 := of_decide_eq_true hh.1
    have hsqrt : Nat.sqrt n < 182 := Nat.sqrt_lt.mpr hbound
    refine Nat.prime_def_le_sqrt.mpr ⟨by omega, ?_⟩
    intro m hm2 hmsqrt hmn
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
    have hple : p ≤ m := Nat.le_of_dvd (show 0 < m by omega) hpm
    have hp181 : p ≤ 181 := by omega
    have hmem := small_prime_cover hp181 hp
    have hnot : ¬ p ∣ n := of_decide_eq_true ((List.all_eq_true.mp hh.2) p hmem)
    exact hnot (dvd_trans hpm hmn)

def check (a factor : ℕ → ℕ) (H : ℕ) : Bool :=
  TotientSieveFast208.checkWith primeCheck a factor H

theorem check_sound {a factor : ℕ → ℕ} {H : ℕ} (hc : check a factor H = true) :
    ∀ n, n ≤ H → a n = Nat.totient n :=
  TotientSieveFast208.checkWith_sound (fun _ hp => primeCheck_sound hp) hc

#print axioms small_prime_sound
#print axioms small_prime_cover
#print axioms primeCheck_sound
#print axioms check_sound
end JSP233.PrimeCover208
