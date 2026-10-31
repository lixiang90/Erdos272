import Erdos272.Arithmetic.LowFactorDivides209
import Erdos272.Arithmetic.FastFullLookup209
import Erdos272.Arithmetic.ForcedCheck209
namespace JSP233.LowFactorSound209
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open FactorFullData209

theorem checkedFast : ForcedCheck209.check FastFullLookup209.marked
    (MarkerSieve209.SmallPrimes 181) 32753=true := by decide +kernel

theorem checked : MarkerSieve209.check marked
    (MarkerSieve209.SmallPrimes 181) 32753=true := by
  have hh := checkedFast
  rw [ForcedCheck209.check_eq] at hh
  simpa only [show FastFullLookup209.marked=marked from funext FastFullLookup209.marked_eq] using hh

theorem prime (n : Nat) (hn : 2≤n) (hnH : n≤32753) (hz : factor n=0) : n.Prime := by
  apply @MarkerSieve209.prime_of_unmarked marked (MarkerSieve209.SmallPrimes 181)
    32753 181 n
    (fun p hp hpB => MarkerSieve209.smallPrimes_cover (by decide : 181<182*182) hp hpB)
    (by decide : 32753<(181+1)^2) hn hnH checked
  simp [marked,hz]

theorem sound (n : Nat) (hn : 2≤n) (hnH : n≤32753) :
    (factor n=0 → n.Prime) ∧
    (factor n≠0 → (factor n).Prime ∧ factor n∣n) := by
  constructor
  · exact prime n hn hnH
  · intro hp
    exact ⟨factor_prime hp,LowFactorDivides209.divides n hn hnH hp⟩

#print axioms checkedFast
#print axioms prime
#print axioms sound
end JSP233.LowFactorSound209

