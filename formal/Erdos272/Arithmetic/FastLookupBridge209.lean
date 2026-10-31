import Erdos272.Arithmetic.FastFullLookup209
import Erdos272.Arithmetic.ForcedDivides209
namespace JSP233.FastLookupBridge209
set_option maxHeartbeats 0
theorem checked_interval (p qlo len q : Nat)
    (hc : MarkerSieve209.checkMultiples FastFullLookup209.marked p (p * qlo) len = true)
    (hlo : qlo ≤ q) (hhi : q < qlo + len) : FactorFullData209.marked (p * q) = true := by
  have hh := @MarkerSieve209.checked_interval FastFullLookup209.marked p qlo len q hc hlo hhi
  simpa only [FastFullLookup209.marked_eq] using hh
theorem divides_of_check (lo len n : Nat)
    (hc : ForcedDivides209.check FastFullLookup209.factor lo len = true)
    (hlo : lo ≤ n) (hhi : n < lo + len) (hp : FactorFullData209.factor n ≠ 0) :
    FactorFullData209.factor n ∣ n := by
  have hp' : FastFullLookup209.factor n ≠ 0 := by simpa only [FastFullLookup209.factor_eq] using hp
  have hh := @ForcedDivides209.check_sound FastFullLookup209.factor lo len n hc hlo hhi hp'
  simpa only [FastFullLookup209.factor_eq] using hh
#print axioms checked_interval
#print axioms divides_of_check
end JSP233.FastLookupBridge209
