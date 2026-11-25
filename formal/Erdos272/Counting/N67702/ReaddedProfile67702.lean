module

public import Erdos272.Counting.N67702.PreparedCountBounds67702
public import Erdos272.Resources.N291012.RootModel291012

@[expose] public section

namespace JSP233.RawProfile67702
open StarCompletion APGeometry HarmonicAbel29 APPrepare49 PreparedClasses50
open PreparedWitness48 RestrictedWitness44 MiddleCoordinates51 LongTerminal35 DenseDeletion40
open PrivatePairExistence LocalRecovery208 CovarianceFamily214 RootModel291012
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem actual_raw_with_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    {alpha beta fee s : ℝ} (g : Start N c L R F P T) (hN : 19≤N) (hhigh : N≤720896)
    (hsmall : ((SmallAP (GenericRecovery291012.Readded N 12 F (c : ℤ))).card : ℝ)≤2*(N : ℝ)+s)
    (hex : ((EX (PreparedAP (GenericRecovery291012.Readded N 12 F (c : ℤ)) c L) R).card : ℝ)≤
      (129/200 : ℝ)*L*((N : ℝ)-R)+Width N L R*Harmonic N+N-
        alpha*N-beta*Width N L R+fee) :
    Recovery208.WidthProfile L (Width N L R)≤MiddleCost L+GeometryCost N L (Width N L R)+
      (N : ℝ)/4+(Omitted N c F).card-2*N+L-2*c+s-alpha*N-beta*Width N L R+fee := by
  let G := GenericRecovery291012.Readded N 12 F (c : ℤ)
  have hGF : G⊆F := Finset.sdiff_subset
  have hG : Legal (Ground N) G :=
    ⟨fun S hS=>g.legal.1 S (hGF hS),fun S hS U hU hne=>g.legal.2 S (hGF hS) U (hGF hU) hne⟩
  have hsub := GenericRecovery291012.actual_retained_subset_readded N 12 F (c : ℤ)
  have hroot : ∀S∈G,¬IsAP S→(c : ℤ)∈S := GenericRecovery291012.actual_readded_root g.root
  have ha := TerminalDeficit51.actual_avoider_readdition N 12 F (c : ℤ)
  have hout : ∀S∈G,(c : ℤ)∉S→(∃u∈S,u≤(L : ℤ))∧∃v∈S,(R : ℤ)≤v := by
    intro S hS hcS
    have hv : S∈Avoiders G (c : ℤ) := Finset.mem_filter.mpr ⟨hS,hcS⟩
    change Avoiders G (c : ℤ)=_ at ha
    rw [ha] at hv
    exact g.outside S (Finset.mem_filter.mp hv).1 hcS
  obtain ⟨x,p,hx⟩ := actual_prepared_witness_choices hG hroot
    (by exact_mod_cast g.root_left.le : (c : ℤ)≤L)
    (by exact_mod_cast g.left_right : (L : ℤ)≤R) (hsub g.left_member) g.left_avoids g.left_upper
  have hp := PreparationBounds67702.actual_preparation_custom hN (by omega : N≤853476)
    g.root_mem hG g.root_left (g.left_right.trans g.right_ground) hroot
    (hsub g.right_member) g.right_avoids g.right_lower hsmall
  have hj := PreparationBounds67702.actual_middle_custom x p hG g.root_left g.left_right g.right_ground
    (hsub g.right_member) g.right_lower hroot hout
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.2.1,(hx S hS).2.2.2.2.1,(hx S hS).2.2.2.2.2⟩)
  have hm := CovarianceFamily214.actual_prepared_middle_local x p (by have h:=g.root_left;omega : 1≤L)
    hhigh g.root_left.le g.left_right g.right_ground hG hroot (hsub g.right_member) g.right_lower
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.1,(hx S hS).2.2.2.1⟩)
  have hcard : (G.card : ℝ)+(Omitted N c F).card=F.card := by
    exact_mod_cast GenericRecovery291012.actual_card_identity N 12 F (c : ℤ)
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1≤N) g.near_card
  dsimp only [Width] at hex ⊢
  rw [RawRecovery208.width_profile_eq]
  dsimp only [PreparationCost] at hp
  dsimp only [GeometryCost]
  linarith only [hp,hj,hm,hex,hcard,hb]

#print axioms actual_raw_with_bounds
end
end JSP233.RawProfile67702
