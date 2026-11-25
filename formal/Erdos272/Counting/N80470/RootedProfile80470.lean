module

public import Erdos272.Counting.N80470.RootedPreparation80470
public import Erdos272.Resources.N291012.RootModel291012
public import Erdos272.Retention.N86412.RetainedIntervals86412

@[expose] public section

namespace JSP233.RootedProfile80470
open StarCompletion APGeometry HarmonicAbel29 APPrepare49 PreparedClasses50
open PreparedWitness48 RestrictedWitness44 MiddleCoordinates51 LongTerminal35 DenseDeletion40
open PrivatePairExistence LocalRecovery208 CovarianceFamily214 RootModel291012
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem actual_small_root {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 56400≤N) (hhigh : N≤88403)
    (hleft : (L : ℝ)<(1/16 : ℝ)*N) (hspan : L+3≤R) :
    ∀ S∈SmallAP (GenericRecovery291012.Readded N 12 F (c : ℤ)),(c : ℤ)∈S := by
  have hi := RetainedIntervals86412.actual_avoiders_intervals g hN hhigh hleft
  have ha := TerminalDeficit51.actual_avoider_readdition N 12 F (c : ℤ)
  change Avoiders (GenericRecovery291012.Readded N 12 F (c : ℤ)) (c : ℤ)=_ at ha
  intro S hS
  by_contra hcS
  have hm := APPrepare49.actual_small_AP_member hS
  have hv : S∈Avoiders (GenericRecovery291012.Readded N 12 F (c : ℤ)) (c : ℤ) :=
    Finset.mem_filter.mpr ⟨hm.1,hcS⟩
  rw [ha] at hv
  obtain ⟨a,b,_hca,haL,hRb,_hbN,hrep⟩ := hi S hv
  have hI : Finset.Icc (L : ℤ) (R : ℤ)⊆S := by
    rw [hrep]
    intro z hz
    obtain ⟨hLz,hzR⟩ := Finset.mem_Icc.mp hz
    change z∈Finset.Icc (a : ℤ) (b : ℤ)
    exact Finset.mem_Icc.mpr
      ⟨(by exact_mod_cast haL : (a : ℤ)≤L).trans hLz,
       hzR.trans (by exact_mod_cast hRb : (R : ℤ)≤b)⟩
  have hcount := Finset.card_le_card hI
  have hfour : 4≤(Finset.Icc (L : ℤ) (R : ℤ)).card := by
    simp only [Int.card_Icc]
    omega
  omega

theorem actual_raw {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 19≤N) (hhigh : N≤720896)
    (hsmall : ∀ S∈SmallAP (GenericRecovery291012.Readded N 12 F (c : ℤ)),(c : ℤ)∈S) :
    Recovery208.WidthProfile L (Width N L R)≤MiddleCost L+
      GeometryCost N L (Width N L R)+(N : ℝ)/4-(N : ℝ)/2+(Omitted N c F).card := by
  let G := GenericRecovery291012.Readded N 12 F (c : ℤ)
  have hGF : G⊆F := Finset.sdiff_subset
  have hG : Legal (Ground N) G :=
    ⟨fun S hS => g.legal.1 S (hGF hS),fun S hS U hU hSU => g.legal.2 S (hGF hS) U (hGF hU) hSU⟩
  have hsub := GenericRecovery291012.actual_retained_subset_readded N 12 F (c : ℤ)
  have hGroot : ∀ S∈G,¬IsAP S→(c : ℤ)∈S := GenericRecovery291012.actual_readded_root g.root
  have ha := TerminalDeficit51.actual_avoider_readdition N 12 F (c : ℤ)
  have hout : ∀ S∈G,(c : ℤ)∉S→
      (∃ u∈S,u≤(L : ℤ))∧∃ v∈S,(R : ℤ)≤v := by
    intro S hS hcS
    have hv : S∈Avoiders G (c : ℤ) := Finset.mem_filter.mpr ⟨hS,hcS⟩
    change Avoiders G (c : ℤ)=_ at ha
    rw [ha] at hv
    exact g.outside S (Finset.mem_filter.mp hv).1 hcS
  obtain ⟨x,p,hx⟩ := actual_prepared_witness_choices hG hGroot
    (by exact_mod_cast g.root_left.le : (c : ℤ)≤L)
    (by exact_mod_cast g.left_right : (L : ℤ)≤R) (hsub g.left_member) g.left_avoids g.left_upper
  have hlocal := RootedPreparation80470.actual_losses x p hN (by omega : N≤853476)
    g.root_mem hG g.root_left g.left_right g.right_ground hGroot
    (hsub g.right_member) g.right_avoids g.right_lower hout
    (fun S hS => ⟨(hx S hS).1,(hx S hS).2.2.1,(hx S hS).2.2.2.2.1,(hx S hS).2.2.2.2.2⟩) hsmall
  have hm := actual_prepared_middle_local x p (by have h:=g.root_left; omega : 1≤L) hhigh
    g.root_left.le g.left_right g.right_ground hG hGroot (hsub g.right_member) g.right_lower
    (fun S hS => ⟨(hx S hS).1,(hx S hS).2.1,(hx S hS).2.2.2.1⟩)
  have hcard : (G.card : ℝ)+(Omitted N c F).card=F.card := by
    exact_mod_cast GenericRecovery291012.actual_card_identity N 12 F (c : ℤ)
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1≤N) g.near_card
  dsimp only [Width]
  rw [RawRecovery208.width_profile_eq]
  linarith only [hlocal,hm,hcard,hb]

#print axioms actual_small_root
#print axioms actual_raw
end
end JSP233.RootedProfile80470
