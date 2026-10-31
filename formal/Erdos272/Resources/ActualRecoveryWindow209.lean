import Erdos272.Arithmetic.TotientWindow209
import Erdos272.Arithmetic.TotientInputBridge209
import Erdos272.Resources.OriginalTerminal208

namespace JSP233.ActualRecoveryWindow209
open StarCompletion APGeometry ActualRecoveryChain208 DenseDeletion40
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem actual_totient_inputs (N : ℕ) (hN : N ≤ 720896) :
    LocalResourceRecovery208.TotientInputs N :=
  TotientInputBridge209.inputs_of_bounds TotientWindow209.bounds N hN

theorem actual_four_stage {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) :
    (L : ℝ)<(5/251 : ℝ)*N ∧ ((L : ℝ)+(N-R))<(5/148 : ℝ)*N := by
  have hh := g.high
  exact ActualRecoveryChain208.actual_four_stage g (actual_totient_inputs N (by omega))

theorem actual_recovered_original {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T)
    (hi : ∀ S ∈ Avoiders (Retained N 11 F) (c : ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) :
    F.card ≤ B N := by
  have hh := g.high
  have hne : (Avoiders (Retained N 11 F) (c : ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩⟩
  exact OriginalTerminal208.actual_recovered_original g
    (actual_totient_inputs N (by omega)) hne hi

#print axioms actual_totient_inputs
#print axioms actual_four_stage
#print axioms actual_recovered_original
end
end JSP233.ActualRecoveryWindow209
