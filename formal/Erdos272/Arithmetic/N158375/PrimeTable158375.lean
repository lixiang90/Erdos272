module

public import Erdos272.Core.N180000.AnalyticCore180000

@[expose] public section

namespace JSP233.PrimeTable158375
open CoreUnionSource200000
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def primes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761}

def smallDivisors : Finset ℕ := {2,3,5,7,11,13,17,19,23}
def admissible (q : ℕ) : Prop := 2 ≤ q ∧ ∀ p ∈ smallDivisors, q=p ∨ q%p ≠ 0
instance (q : ℕ) : Decidable (admissible q) := by unfold admissible; infer_instance
def candidates : Finset ℕ := (Finset.range 768).filter admissible

theorem candidates_correct : candidates = primes := by decide +kernel
#print axioms candidates_correct

theorem prime_admissible {q : ℕ} (hq : q.Prime) : admissible q := by
  refine ⟨hq.two_le, ?_⟩
  intro p hp
  by_cases he : q=p
  · exact Or.inl he
  · apply Or.inr
    intro hz
    have hpone : p ≠ 1 := by
      have hc : ∀ p ∈ smallDivisors, p ≠ 1 := by decide +kernel
      exact hc p hp
    have hv := hq.eq_one_or_self_of_dvd p (Nat.dvd_of_mod_eq_zero hz)
    omega
#print axioms prime_admissible

theorem all_primes_small {a : ℕ} (ha : a ≤ 768) :
    AllPrimes a ⊆ primes.filter (fun q => q < a) := by
  intro q hq
  obtain ⟨hr, hp⟩ := Finset.mem_filter.mp hq
  have hqa := Finset.mem_range.mp hr
  have hm : q ∈ candidates := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), prime_admissible hp⟩
  rw [candidates_correct] at hm
  exact Finset.mem_filter.mpr ⟨hm, hqa⟩
#print axioms all_primes_small

def smallUnit (a : ℕ) : ℕ := a.choose 2-
  ∑ q ∈ primes.filter (fun q => q < a), Weight a q

theorem smallUnit_le {a : ℕ} (ha : a ≤ 768) : smallUnit a ≤ UnitBound a := by
  have hs := Finset.sum_le_sum_of_subset (all_primes_small ha) (f := Weight a)
  unfold smallUnit UnitBound
  omega
#print axioms smallUnit_le
end
end JSP233.PrimeTable158375
