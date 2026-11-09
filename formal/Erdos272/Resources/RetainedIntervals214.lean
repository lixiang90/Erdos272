module

public import Erdos272.Resources.OriginalTerminal214
public import Erdos272.Resources.RetainedIntervals213

@[expose] public section
namespace JSP233.RetainedIntervals214
open StarCompletion APGeometry DenseDeletion40 LongTerminal35
open RecoveryResource213 ActualRecoveryChain214
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
theorem actual_left {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : InitialGeometry N c L R F P T) (hN : 653292≤N) (hhigh : N≤656184) :
    (L : ℝ)<(5/97 : ℝ)*N := by
  have hh := (actual_initial_bounds g hN hhigh).1
  norm_num [RecoveryLocalization212.Div] at hh
  nlinarith only [hh]
theorem actual_geometry {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : InitialGeometry N c L R F P T) (hN : 653292≤N) (hhigh : N≤656184) :
    Geometry N c L R F P T :=
  ⟨g,RetainedIntervals213.actual_interval_core g (actual_left g hN hhigh)⟩
theorem actual_recovered_original {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : InitialGeometry N c L R F P T) (hN : 653292≤N) (hhigh : N≤656184) : F.card≤B N := by
  have hl := actual_left g hN hhigh
  have hne : (Avoiders (Retained N 11 F) (c : ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩⟩
  exact OriginalTerminal214.actual_recovered_original (actual_geometry g hN hhigh) hN hhigh hne
    (RetainedIntervals213.actual_avoiders_intervals g hl)
#print axioms actual_left
#print axioms actual_geometry
#print axioms actual_recovered_original
end
end JSP233.RetainedIntervals214
