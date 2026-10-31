import Erdos272.Arithmetic.SourceLookupFast208

/-! Composite-marker coverage avoids a separate long trial division for each
large prime.  Coverage is checked on multiples of a proved prime cover.
The proposed marker is arbitrary and is not trusted. -/
namespace JSP233.MarkerSieve209
set_option maxHeartbeats 0

def checkMultiples (marked : Nat → Bool) (p : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | n, k + 1 => marked n && checkMultiples marked p (n + p) k

theorem checkMultiples_sound {marked : Nat → Bool} {p n k : Nat}
    (hc : checkMultiples marked p n k = true) :
    ∀ j, j < k → marked (n + p * j) = true := by
  induction k generalizing n with
  | zero => intro j hj; omega
  | succ k ih =>
    obtain ⟨hh, hc'⟩ : marked n = true ∧ checkMultiples marked p (n + p) k = true := by
      simpa only [checkMultiples, Bool.and_eq_true_iff] using hc
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using hh
    · have h := ih hc' (j - 1) (by omega)
      have heq : n + p + p * (j - 1) = n + p * j := by
        have hjs : j - 1 + 1 = j := by omega
        nlinarith only [congrArg (p * ·) hjs]
      simpa only [heq] using h

theorem checkMultiples_append (marked : Nat → Bool) (p n k l : Nat) :
    checkMultiples marked p n (k + l) =
      (checkMultiples marked p n k && checkMultiples marked p (n + p * k) l) := by
  induction k generalizing n with
  | zero => simp [checkMultiples]
  | succ k ih =>
    rw [Nat.succ_add, checkMultiples, checkMultiples, ih]
    have heq : n + p + p * k = n + p * (k + 1) := by ring
    rw [heq, Bool.and_assoc]

theorem checked_interval {marked : Nat → Bool} {p qlo len q : Nat}
    (hc : checkMultiples marked p (p * qlo) len = true)
    (hlo : qlo ≤ q) (hhi : q < qlo + len) : marked (p * q) = true := by
  have hh := checkMultiples_sound hc (q - qlo) (by omega)
  have hq : q - qlo + qlo = q := by omega
  have heq : p * qlo + p * (q - qlo) = p * q := by
    nlinarith only [congrArg (p * ·) hq]
  simpa only [heq] using hh

def checkRow (marked : Nat → Bool) (H p : Nat) : Bool :=
  checkMultiples marked p (2 * p) (H / p - 1)

def check (marked : Nat → Bool) (P : List Nat) (H : Nat) : Bool :=
  P.all (fun p => checkRow marked H p)

theorem checkRow_sound {marked : Nat → Bool} {H p q : Nat}
    (hp : 0 < p) (hq : 2 ≤ q) (hpq : p * q ≤ H)
    (hc : checkRow marked H p = true) : marked (p * q) = true := by
  have hqH : q ≤ H / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa only [Nat.mul_comm] using hpq)
  have hj : q - 2 < H / p - 1 := by omega
  have hh := checkMultiples_sound hc (q - 2) hj
  have heq : 2 * p + p * (q - 2) = p * q := by
    have heq' : q - 2 + 2 = q := by omega
    nlinarith only [congrArg (p * ·) heq']
  simpa only [heq] using hh

theorem prime_of_unmarked_of_rows {marked : Nat → Bool} {P : List Nat} {H B n : Nat}
    (hcover : ∀ p, p.Prime → p ≤ B → p ∈ P)
    (hH : H < (B + 1)^2) (hn2 : 2 ≤ n) (hnH : n ≤ H)
    (hrows : ∀ p, p.Prime → p ∈ P → ∀ q, 2 ≤ q → p * q ≤ H → marked (p * q) = true)
    (hn : marked n = false) : n.Prime := by
  refine Nat.prime_def_le_sqrt.mpr ⟨hn2, ?_⟩
  intro m hm2 hmsqrt hmn
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
  have hple : p ≤ m := Nat.le_of_dvd (by omega : 0 < m) hpm
  have hsqrt : Nat.sqrt n < B + 1 := Nat.sqrt_lt.mpr (by simpa only [pow_two] using hnH.trans_lt hH)
  have hpB : p ≤ B := by omega
  have hpP := hcover p hp hpB
  have hpn : p ∣ n := dvd_trans hpm hmn
  have heq : p * (n / p) = n := Nat.mul_div_cancel' hpn
  have hpltn : p < n := (hple.trans hmsqrt).trans_lt (Nat.sqrt_lt_self (by omega))
  have hq2 : 2 ≤ n / p := by
    have hppos := hp.pos
    by_contra h
    have hq : n / p ≤ 1 := by omega
    have hnle : n ≤ p := by nlinarith only [heq, hq]
    omega
  have hmarked := hrows p hp hpP (n / p) hq2 (heq.le.trans hnH)
  rw [heq] at hmarked
  simp only [hn, Bool.false_eq_true] at hmarked

theorem prime_of_unmarked {marked : Nat → Bool} {P : List Nat} {H B n : Nat}
    (hcover : ∀ p, p.Prime → p ≤ B → p ∈ P)
    (hH : H < (B + 1)^2) (hn2 : 2 ≤ n) (hnH : n ≤ H)
    (hc : check marked P H = true) (hn : marked n = false) : n.Prime := by
  apply prime_of_unmarked_of_rows hcover hH hn2 hnH ?_ hn
  intro p hpPrime hpP q hq hprod
  exact checkRow_sound hpPrime.pos hq hprod ((List.all_eq_true.mp hc) p hpP)

theorem primeCheck_complete {n : Nat} (hp : n.Prime) (hb : n < 182 * 182) :
    PrimeCover208.primeCheck n = true := by
  by_cases hn : n ≤ 181
  · have hm := PrimeCover208.small_prime_cover hn hp
    simpa only [PrimeCover208.primeCheck, if_pos hn] using decide_eq_true hm
  · simp only [PrimeCover208.primeCheck, if_neg hn, Bool.and_eq_true_iff]
    refine ⟨decide_eq_true hb, List.all_eq_true.mpr ?_⟩
    intro p hpP
    have hpp := PrimeCover208.small_prime_sound hpP
    have hple : p ≤ 181 := by
      simp only [PrimeCover208.SmallPrimes, List.mem_cons, List.not_mem_nil, or_false] at hpP
      omega
    apply decide_eq_true
    intro hpn
    have hp1 : p = 1 ∨ p = n := (Nat.dvd_prime hp).mp hpn
    rcases hp1 with hp1 | hpn
    · exact hpp.ne_one hp1
    · omega

def SmallPrimes (B : Nat) : List Nat :=
  ((List.range (B - 1)).map (fun j => j + 2)).filter PrimeCover208.primeCheck

theorem smallPrimes_cover {B p : Nat} (hB : B < 182 * 182) (hp : p.Prime)
    (hpB : p ≤ B) : p ∈ SmallPrimes B := by
  apply List.mem_filter.mpr
  refine ⟨?_, primeCheck_complete hp (hpB.trans_lt hB)⟩
  apply List.mem_map.mpr
  refine ⟨p - 2, ?_, ?_⟩
  · simp only [List.mem_range]
    have hp2 := hp.two_le
    omega
  · have hp2 := hp.two_le
    omega

#print axioms checkRow_sound
#print axioms prime_of_unmarked
#print axioms smallPrimes_cover
end JSP233.MarkerSieve209
