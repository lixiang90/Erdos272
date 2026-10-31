import Erdos272.Resources.RawEndpoint116
namespace JSP233.BootstrapFringe139
open StarCompletion APGeometry DenseDeletion40 LongTerminal35 JointFringe44
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000
theorem joint_count21 : JointCount 21=90 := by
  norm_num [JointCount,ShortCount,Finset.sum_Icc_succ_top]
theorem actual_deleted_avoider_count90 {N c L R : ℕ} {F : Finset (Finset ℤ)}
    (hN : 9261≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hne : (Avoiders (Retained N 11 F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hthin : 24*(L+N-R)≤N) :
    (TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)).card≤90*((L+N-R)-1) := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)
  have hGF : Retained N 11 F⊆F := Finset.sdiff_subset
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have hbad : ∀S∈E,¬IsAP S := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  have hdense : ∀S∈E,N<11*S.card := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
  have hcG := (mem_ground N (c:ℤ)).mp hc
  have hb := TerminalDeficit51.actual_interval_fringe_count 11 21 N c L R F (Retained N 11 F) E
    (by decide) (by decide) (by decide) (by norm_num;exact hN)
    (by omega) hcL hLR hRN (by omega) hGF hEF hF hbad hdense hne hi
  rw [joint_count21] at hb
  exact hb


#print axioms joint_count21
#print axioms actual_deleted_avoider_count90
end
end JSP233.BootstrapFringe139
