module

public import Erdos272.Arithmetic.FastFullLookup209
public import Erdos272.Arithmetic.ForcedDivides209

@[expose] public section
namespace JSP233.LowFactorDivides209
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open FactorFullData209
theorem checkedFast : ForcedDivides209.check FastFullLookup209.factor 2 32752 = true := by decide +kernel

theorem checked : ForcedDivides209.check factor 2 32752 = true := by
  simpa only [show FastFullLookup209.factor = factor from funext FastFullLookup209.factor_eq] using checkedFast

theorem divides (n : Nat) (hn : 2 ≤ n) (hnH : n ≤ 32753) (hp : factor n≠0) : factor n∣n :=
  ForcedDivides209.check_sound checked hn (by omega) hp
#print axioms checked
#print axioms divides
end JSP233.LowFactorDivides209


