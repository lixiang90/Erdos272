module

public import Erdos272.Arithmetic.FastLookupBridge209
public import Erdos272.Arithmetic.FastComputed209
public import Erdos272.Arithmetic.FastDecode208
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section
namespace JSP233.FactorSoundBridge209
open FactorFullData209
set_option maxHeartbeats 0
def Rows : Prop := ∀ p, p.Prime → p ∈ MarkerSieve209.SmallPrimes PrimeBound →
  ∀ q, 2 ≤ q → p*q ≤ Limit → marked (p*q) = true
def Divides : Prop := ∀ n, 32753 < n → n ≤ Limit → factor n ≠ 0 → factor n ∣ n

theorem factor_sound (hrows : Rows) (hdiv : Divides) (n : Nat)
    (hn : 32753 < n) (hnH : n ≤ Limit) :
    (factor n = 0 → n.Prime) ∧ (factor n ≠ 0 → (factor n).Prime ∧ factor n ∣ n) := by
  constructor
  · intro hzero
    apply @MarkerSieve209.prime_of_unmarked_of_rows marked (MarkerSieve209.SmallPrimes PrimeBound) Limit PrimeBound n
      (fun p hp hpB => MarkerSieve209.smallPrimes_cover (by decide : PrimeBound < 182*182) hp hpB)
      (by decide : Limit < (PrimeBound+1)^2) (by omega : 2 ≤ n) hnH hrows
    simp [marked, hzero]
  · intro hp
    exact ⟨factor_prime hp, hdiv n hn hnH hp⟩

def value (n : Nat) : Nat := FastComputed209.value FastDecode208.phi FastFullLookup209.factor 6 n
theorem phi_correct (hrows : Rows) (hdiv : Divides) (n : Nat) (hn : n ≤ Limit) :
    value n = Nat.totient n := by
  unfold value
  rw [FastComputed209.value_eq FastDecode208.phi FastFullLookup209.factor 6 n]
  have hf : ∀ m, 32753 < m → m ≤ Limit →
      (FastFullLookup209.factor m = 0 → m.Prime) ∧
      (FastFullLookup209.factor m ≠ 0 → (FastFullLookup209.factor m).Prime ∧ FastFullLookup209.factor m ∣ m) := by
    intro m hm hmH
    simpa only [FastFullLookup209.factor_eq] using factor_sound hrows hdiv m hm hmH
  have hnfuel : n < 32754 * 2^6 := by
    unfold Limit at hn
    norm_num
    omega
  exact @ComputedTotient209.correct FastDecode208.phi FastFullLookup209.factor Limit
    FastDecode208.phi_correct hf 6 n hn hnfuel
#print axioms factor_sound
#print axioms phi_correct
end JSP233.FactorSoundBridge209
