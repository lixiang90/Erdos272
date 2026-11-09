module

public import Erdos272.Resources.ActualRecoveryChain214
public import Erdos272.Resources.OriginalTerminal213

@[expose] public section
namespace JSP233.OriginalTerminal214
open StarCompletion APGeometry DenseDeletion40
open RecoveryResource213 ActualRecoveryChain214
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
theorem actual_recovered_original {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hN : 653292≤N) (hhigh : N≤656184)
    (hne : (Avoiders (Retained N 11 F) (c : ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c : ℤ),∃a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) : F.card≤B N := by
  have hb := actual_four_stage g hN hhigh
  have hg := g.high
  have hc : 1≤c := by exact_mod_cast ((mem_ground N (c : ℤ)).mp g.root_mem).1
  apply OriginalTerminal213.actual_deleted_restore g.low (by omega) hc g.root_left g.left_right
    g.right_ground _ g.legal hne hi
  nlinarith only [hb.2]
#print axioms actual_recovered_original
end
end JSP233.OriginalTerminal214
