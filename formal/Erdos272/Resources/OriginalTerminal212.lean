import Erdos272.Resources.NativeRestore212
import Erdos272.Resources.ActualRecoveryChain212

namespace JSP233.OriginalTerminal212
open StarCompletion APGeometry DenseDeletion40 TerminalDeficit51 NativeRestore212
open ActualRecoveryChain212
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem actual_deleted_restore {N c L R : ℕ} {F : Finset (Finset ℤ)}
    (hN : 656184 ≤ N) (hhi : N < 2^50) (hc : 1 ≤ c) (hcL : c < L)
    (hLR : L ≤ R) (hRN : R ≤ N)
    (hwidth : (L : ℝ)+(N-R) < (N : ℝ)/(2951/100))
    (hF : Legal (Ground N) F)
    (hne : (Avoiders (Retained N 11 F) (c : ℤ)).Nonempty)
    (hi : ∀ S ∈ Avoiders (Retained N 11 F) (c : ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) : F.card ≤ B N := by
  let E := OmittedAvoiders N 11 F (c : ℤ)
  have hEF : E ⊆ F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have ha := actual_avoider_readdition N 11 F (c : ℤ)
  apply actual_restore hN hhi hc hcL hLR hRN hwidth (G := F\E) rfl hEF hF
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · simpa only [E,ha] using hne
  · simpa only [E,ha] using hi

theorem actual_recovered_original {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hfrontier : LocalResourceRecovery208.TotientInputs N)
    (hne : (Avoiders (Retained N 11 F) (c : ℤ)).Nonempty)
    (hi : ∀ S ∈ Avoiders (Retained N 11 F) (c : ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) : F.card ≤ B N := by
  have hbounds := actual_four_stage g hfrontier
  have hhigh := g.high
  have hc : 1 ≤ c := by exact_mod_cast ((mem_ground N (c : ℤ)).mp g.root_mem).1
  apply actual_deleted_restore g.low (by omega) hc g.root_left g.left_right g.right_ground _ g.legal hne hi
  nlinarith only [hbounds.2]

#print axioms actual_deleted_restore
#print axioms actual_recovered_original
end
end JSP233.OriginalTerminal212
