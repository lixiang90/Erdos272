module

public import Erdos272.Resources.LocalResourceRecovery208
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace JSP233.TotientInputBridge209
set_option maxHeartbeats 0

theorem inputs_of_bounds {H : Nat}
    (hbounds : ∀ t : Nat, t ≤ H →
      ((500000000 / 822467033 : Real) * t - 17 / 200 ≤
          ∑ n ∈ Finset.Icc 1 t, (Nat.totient n : Real) / n) ∧
      ((500000000 / 822467033 : Real) * (t : Real)^2 / 2 - (61 / 200) * t ≤
          ((∑ n ∈ Finset.Icc 2 t, Nat.totient n : Nat) : Real)))
    (N : Nat) (hN : N ≤ H) : LocalResourceRecovery208.TotientInputs N := by
  constructor
  · intro t ht
    simpa only [FrontierDensity208.Rho, TotientRows208.TotientMass] using
      (hbounds t (ht.trans hN)).1
  · intro t ht
    simpa only [FrontierDensity208.Rho, LocalizedMiddle208.TotientTriangle] using
      (hbounds t (ht.trans hN)).2
#print axioms inputs_of_bounds
end JSP233.TotientInputBridge209
