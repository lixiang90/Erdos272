import Erdos272.Resources.RecoveryResource213
import Erdos272.Arithmetic.RecoveryScalar213
namespace JSP233.ActualRecoveryChain213
open StarCompletion APGeometry DenseDeletion40 LocalResourceRecovery208 Recovery208
open RecoveryCaps213 RecoveryResource213 RecoveryScalar213 AlignedPlans212
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_initial_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : InitialGeometry N c L R F P T) (hi : TotientInputs N)
    (hN : 654848≤N) (hhigh : N≤656184) :
    (L : ℝ)<(N : ℝ)/RecoveryLocalization212.Div 1 ∧
      ((L : ℝ)+(N-R))<(N : ℝ)/PreparationWidth 1 := by
  have hc := actual_caps (by omega : 100000≤N) hhigh
  have hn : (654848 : ℝ)≤N := by exact_mod_cast hN
  have hg := initial_global_affine g hi hc
  have h0 := initial_weak hn hg
  have h1 := initial_update hn (initial_reprice g hi hc (by decide : 0≤7) h0)
  exact initial_final hn (initial_reprice g hi hc (by decide : 1≤7) h1)

theorem actual_four_stage {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : TotientInputs N)
    (hN : 654848≤N) (hhigh : N≤656184) :
    (L : ℝ)<(N : ℝ)/50 ∧ ((L : ℝ)+(N-R))<(N : ℝ)/(2951/100) := by
  have hc := actual_caps (by omega : 100000≤N) hhigh
  have hn : (654848 : ℝ)≤N := by exact_mod_cast hN
  have h2 := actual_initial_bounds g.toInitialGeometry hi hN hhigh
  have h3 := first_weak hn (actual_local_affine (r:=1) g hi hc (by decide) (by decide) (by decide : 1≤7) h2.1 h2.2)
  have h4 := first_update hn (actual_local_affine (r:=1) g hi hc (by decide) (by decide) (by decide : 2≤7) h3 h2.2)
  have h5 := first_final hn (actual_local_affine (r:=1) g hi hc (by decide) (by decide) (by decide : 3≤7) h4 h2.2)
  have h6 := second_weak hn (actual_local_affine (r:=2) g hi hc (by decide) (by decide) (by decide : 4≤7) h5.1 h5.2)
  have h7 := second_update hn (actual_local_affine (r:=2) g hi hc (by decide) (by decide) (by decide : 5≤7) h6 h5.2)
  have h8 := second_final hn (actual_local_affine (r:=2) g hi hc (by decide) (by decide) (by decide : 6≤7) h7 h5.2)
  have h9 := third_weak hn (actual_local_affine (r:=3) g hi hc (by decide) (by decide) (by decide : 6≤7) h8.1 h8.2)
  have ht := third_final hn (actual_local_affine (r:=3) g hi hc (by decide) (by decide) (by decide : 7≤7) h9 h8.2)
  simpa [RecoveryLocalization212.Div] using ht
#print axioms actual_initial_bounds
#print axioms actual_four_stage
end
end JSP233.ActualRecoveryChain213
