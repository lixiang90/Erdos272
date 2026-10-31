import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.MarkerSieve209
namespace JSP233.SplitChecks209
set_option maxHeartbeats 0

theorem marked_join (marked : Nat → Bool) (p n k l : Nat)
    (hk : MarkerSieve209.checkMultiples marked p n k = true)
    (hl : MarkerSieve209.checkMultiples marked p (n+p*k) l = true) :
    MarkerSieve209.checkMultiples marked p n (k+l) = true := by
  rw [MarkerSieve209.checkMultiples_append, hk, hl]
  rfl

theorem frontier_join (a : Nat → Nat) (k n f u fMid uMid l fEnd uEnd : Nat)
    (hk : DualFrontier209.checkFrom a n k f u fMid uMid = true)
    (hl : DualFrontier209.checkFrom a (n+k) l fMid uMid fEnd uEnd = true) :
    DualFrontier209.checkFrom a n (k+l) f u fEnd uEnd = true := by
  induction k generalizing n f u with
  | zero =>
    have he : f = fMid ∧ u = uMid := of_decide_eq_true hk
    rcases he with ⟨rfl,rfl⟩
    simpa only [Nat.zero_add, Nat.add_zero] using hl
  | succ k ih =>
    have hp : DualFrontier209.Good (n+1)
        (f+FrontierCheck209.Grid*a (n+1)/(n+1)) (u+if n+1=1 then 0 else a (n+1)) ∧
        DualFrontier209.checkFrom a (n+1) k
          (f+FrontierCheck209.Grid*a (n+1)/(n+1)) (u+if n+1=1 then 0 else a (n+1)) fMid uMid = true := by
      simpa only [DualFrontier209.checkFrom, Bool.and_eq_true_iff, decide_eq_true_eq] using hk
    have hnext : DualFrontier209.checkFrom a (n+1+k) l fMid uMid fEnd uEnd = true := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hl
    have htail := ih (n+1) _ _ hp.2 hnext
    simpa only [Nat.succ_add, DualFrontier209.checkFrom, Bool.and_eq_true_iff,
      decide_eq_true_eq] using And.intro hp.1 htail
#print axioms marked_join
#print axioms frontier_join
end JSP233.SplitChecks209
