import Erdos272.Arithmetic.SigmaPrefix209

namespace JSP233.SigmaPrefixBlocks209
set_option maxHeartbeats 0
set_option Elab.async false

theorem checked_join (a : Nat → Nat)
    (k n d w dMid wMid l dEnd wEnd : Nat)
    (hk : SigmaPrefix209.checkFrom a n k d w dMid wMid = true)
    (hl : SigmaPrefix209.checkFrom a (n+k) l dMid wMid dEnd wEnd = true) :
    SigmaPrefix209.checkFrom a n (k+l) d w dEnd wEnd = true := by
  induction k generalizing n d w with
  | zero =>
    have he : d=dMid ∧ w=wMid := of_decide_eq_true hk
    rcases he with ⟨rfl,rfl⟩
    simpa only [Nat.zero_add, Nat.add_zero] using hl
  | succ k ih =>
    have hp : (31 ≤ n+1 → SigmaPrefix209.Good (n+1) (w+d)) ∧
        SigmaPrefix209.checkFrom a (n+1) k (d+a (n+1)) (w+d) dMid wMid = true := by
      simpa only [SigmaPrefix209.checkFrom, ForcedCheck209.withNat_eq,
        Bool.and_eq_true_iff, decide_eq_true_eq] using hk
    have hnext : SigmaPrefix209.checkFrom a (n+1+k) l dMid wMid dEnd wEnd = true := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hl
    have htail := ih (n+1) _ _ hp.2 hnext
    simpa only [Nat.succ_add, SigmaPrefix209.checkFrom,
      ForcedCheck209.withNat_eq, Bool.and_eq_true_iff,
      decide_eq_true_eq] using And.intro hp.1 htail

#print axioms checked_join
end JSP233.SigmaPrefixBlocks209
