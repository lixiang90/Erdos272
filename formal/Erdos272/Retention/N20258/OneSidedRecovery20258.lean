module

public import Erdos272.Retention.N20258.RootEnvelope20258
public import Erdos272.Retention.N20258.RootIntervals20258
public import Erdos272.Retention.N20258.RootProgressions20258
public import Erdos272.Retention.N20258.RootedSupply20258
public import Erdos272.Retention.N20258.DirectRestore20258
public import Erdos272.Counting.N94488.HalfTrace94488

@[expose] public section
namespace JSP233.OneSidedRecovery20258
open StarCompletion DenseDeletion40 RootModel291012
open scoped Classical
noncomputable section
set_option autoImplicit false

/-- Complete recovery of the original family from either orientation of
the one-sided start. The deleted members are included in the conclusion. -/
theorem actual_upper {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (lo : 19227 ≤ N) (hi : N < 2^16) (g : Start N c L R F P T) : F.card ≤ B N := by
  have raw := RootEnvelope20258.actual_profile (by omega : 19227 ≤ N) hi g
  have axes := RootDimensions20258.actual_axes (by omega : 19227 ≤ N) hi
    g.root_mem g.legal g.near_card g.root_left g.left_right g.right_ground g.root
    g.right_member g.right_avoids g.right_lower g.left_member g.left_avoids g.left_upper g.outside
  have unit := RootProgressions20258.actual_unit lo hi g raw
  have large := RootProgressions20258.actual_size lo hi g raw
  have iv := RootIntervals20258.actual_intervals g unit
  have core := RootIntervals20258.actual_core g iv
  have left : 6*L < N := by exact_mod_cast (show 6*(L : ℝ) < N by linarith only [axes.1])
  have width : Width N L R < (N : ℝ)/4 := axes.2
  have eSub : Omitted N c F ⊆ F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 12 F)
  have paid := HalfTrace94488.actual_high_density_card
    (by have h := g.root_left; omega : 1 ≤ L) g.left_right g.right_ground g.legal eSub
    (fun _ hs => (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2.1) core (by
      intro S hs
      have h := large S (eSub hs) (Finset.mem_filter.mp hs).2
      have r : 2*(N : ℝ) < 3*S.card := by exact_mod_cast h
      linarith only [r,width,Nat.cast_nonneg (α := ℝ) N])
  have wr : Width N L R = ((L+(N-R) : ℕ) : ℝ) := by
    simp only [Width,Nat.cast_add,Nat.cast_sub g.right_ground]
  rw [wr] at paid width
  have count : (Omitted N c F).card+1 ≤ L+(N-R) := by
    exact_mod_cast (show ((Omitted N c F).card : ℝ)+1 ≤ (L+(N-R) : ℕ) by linarith only [paid])
  have w : 4*(L+(N-R)) < N := by
    exact_mod_cast (show 4*((L+(N-R) : ℕ) : ℝ) < N by linarith only [width])
  have gates := RootedSupply20258.actual_gates lo hi g left count unit
  exact DirectRestore20258.actual_restore_with_supply g (by omega) (by omega)
    (ShortSupply20258.of_gates (by omega) g.root_left g.left_right g.right_ground gates)
    count (by omega) iv

#print axioms actual_upper
end
end JSP233.OneSidedRecovery20258
