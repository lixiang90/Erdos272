module

public import Erdos272.Resources.NativeRestore218
public import Erdos272.Counting.DensePair218
public import Erdos272.Counting.UnitAvoider218
public import Erdos272.Geometry.RetainedIntervals218

@[expose] public section

/-! The terminal consumes the same original Start, its actual omitted
avoiders, their proved density-six property, and native width 29. -/
namespace JSP233.OriginalTerminal218
open StarCompletion APGeometry DenseDeletion40 TerminalDeficit51
open InitialProfile218 UnitCount218 UnitAvoider218 DensePair218
open RetainedIntervals218 LongTerminal35
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_recovered_original {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 642498≤N) (hhigh : N≤653292)
    (hleft : (L : ℝ)<(5/97 : ℝ)*N)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/29) : F.card≤B N := by
  let E := OmittedAvoiders N 11 F (c : ℤ)
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have hbad : ∀S∈E,¬IsAP S := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  have havoid : ∀S∈E,(c : ℤ)∉S := fun S hS => (Finset.mem_filter.mp hS).2
  have hdense : ∀S∈E,N<6*S.card := by
    intro S hS
    have hs := actual_omitter_size hN hhigh g (actual_avoid_unit_width_count g)
      (hEF hS) (hbad S hS) (havoid S hS)
    norm_num [Tau] at hs
    have hn : (0 : ℝ)≤N := Nat.cast_nonneg _
    have hd : (N : ℝ)<6*S.card := by nlinarith only [hs,hn]
    exact_mod_cast hd
  have hne : (Avoiders (Retained N 11 F) (c : ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩⟩
  have hi := actual_avoiders_intervals g hN hhigh hleft
  have ha := actual_avoider_readdition N 11 F (c : ℤ)
  have hc : 1≤c := by exact_mod_cast ((mem_ground N (c : ℤ)).mp g.root_mem).1
  apply NativeRestore218.actual_restore hN (by omega : N<2^50) hc g.root_left
    g.left_right g.right_ground hwidth (G := F\E) rfl hEF g.legal hbad hdense havoid
  · simpa only [E,ha] using hne
  · simpa only [E,ha] using hi

#print axioms actual_recovered_original
end
end JSP233.OriginalTerminal218
