module

public import Erdos272.Resources.AffineWitness47
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section
namespace JSP233.PrimorialValue47
open PrimorialPrefix46
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 0

def Primes19 : Finset ℕ :=
  {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67}

theorem primes19_finite_data : Primes19.card=19 ∧
    (∀p∈Primes19,p.Prime ∧ p≤67) ∧
    (∀q∈Finset.range 68,q.Prime → q∈Primes19) := by decide

theorem actual_first_primes19 : FirstPrimes 19=Primes19 := by
  have hi : ∀p∈Primes19,∀q,q.Prime → q∉Primes19 → p≤q := by
    intro p hp q hq hqn
    have hp67 := (primes19_finite_data.2.1 p hp).2
    have hq67 : 67<q := by
      by_contra hn
      have hqr : q∈Finset.range 68 := Finset.mem_range.mpr (by omega)
      exact hqn (primes19_finite_data.2.2 q hqr hq)
    omega
  have hs : Primes19⊆FirstPrimes 19 := by
    intro p hp
    by_contra hpn
    have hn : ¬FirstPrimes 19⊆Primes19 := by
      intro hsub
      have heq := Finset.eq_of_subset_of_card_le hsub
        (by rw [first_primes_card,primes19_finite_data.1])
      exact hpn (by rw [heq];exact hp)
    obtain ⟨q,hq,hqn⟩ := Finset.not_subset.mp hn
    have hpq := hi p hp q (first_primes_prime 19 q hq) hqn
    have hqp := first_primes_initial 19 q p hq (primes19_finite_data.2.1 p hp).1 hpn
    have heq : p=q := Nat.le_antisymm hpq hqp
    exact hqn (heq ▸ hp)
  exact (Finset.eq_of_subset_of_card_le hs
    (by rw [first_primes_card,primes19_finite_data.1])).symm

theorem actual_primorial19 : Primorial 19=7858321551080267055879090 := by
  unfold Primorial
  rw [actual_first_primes19]
  norm_num [Primes19]

#print axioms primes19_finite_data
#print axioms actual_first_primes19
#print axioms actual_primorial19
end
end JSP233.PrimorialValue47
