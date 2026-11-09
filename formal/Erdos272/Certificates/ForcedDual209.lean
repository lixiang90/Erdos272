module

public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.ForcedCheck209

@[expose] public section

/-! Force numeric accumulators before the next step of the dual frontier
check. Both the lower and upper inequalities remain in the specification. -/
namespace JSP233.ForcedDual209
open ForcedCheck209 (withNat withNat_eq)
set_option maxHeartbeats 0
set_option Elab.async false

def checkFrom (a : Nat → Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | _, 0, f, u, fEnd, uEnd => decide (f = fEnd ∧ u = uEnd)
  | n, k + 1, f, u, fEnd, uEnd =>
    withNat (n + 1) (fun t =>
    withNat (a t) (fun ph =>
    withNat (f + FrontierCheck209.Grid * ph / t) (fun f' =>
    withNat (u + if t = 1 then 0 else ph) (fun u' =>
      decide (DualFrontier209.Good t f' u') &&
        checkFrom a t k f' u' fEnd uEnd))))

theorem checkFrom_eq (a : Nat → Nat) (n k f u fEnd uEnd : Nat) :
    checkFrom a n k f u fEnd uEnd =
      DualFrontier209.checkFrom a n k f u fEnd uEnd := by
  induction k generalizing n f u with
  | zero => rfl
  | succ k ih =>
    simp only [checkFrom, withNat_eq, DualFrontier209.checkFrom, ih]

theorem checked {a : Nat → Nat} {n k f u fEnd uEnd : Nat}
    (h : checkFrom a n k f u fEnd uEnd = true) :
    DualFrontier209.checkFrom a n k f u fEnd uEnd = true :=
  (checkFrom_eq a n k f u fEnd uEnd).symm.trans h

#print axioms checkFrom_eq
#print axioms checked
end JSP233.ForcedDual209
