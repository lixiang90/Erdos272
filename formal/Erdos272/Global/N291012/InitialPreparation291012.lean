module

public import Erdos272.Resources.N291012.RootModel291012
public import Erdos272.Global.N291012.CrossGap291012
public import Erdos272.Global.N291012.StarStart291012
public import Erdos272.Resources.RetainedIntervals213
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

namespace JSP233.InitialPreparation291012
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29
open FamilyReflect43 OutsideEnvelope43 Reflect37 WitnessInterval43 RetainedIntervals213 CrossGap291012
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem retained_near {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 291012 ≤ N) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    (N : ℝ)^2/2 ≤ (Retained N 12 F).card+146*(N : ℝ) := by
  have hd := RootModel291012.deleted_affine (by omega : 15853 ≤ N) hF
  have hp := actual_deletion_card_identity N 12 F
  have hdR : ((Deleted N 12 F).card : ℝ) ≤ 144*(N : ℝ)+1296 := by exact_mod_cast hd
  have hpR : ((Retained N 12 F).card : ℝ)+(Deleted N 12 F).card = F.card := by exact_mod_cast hp
  have hn : (N.choose 2 : ℝ)+1 ≤ F.card := by
    exact_mod_cast (show N.choose 2+1 ≤ F.card by unfold B at hcard; omega)
  rw [Nat.cast_choose_two] at hn
  have hnr : (291012 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith only [hdR, hpR, hn, hnr]

theorem actual_retained_above_cross_gap {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 291012 ≤ N) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    17*(N : ℝ)^2/36 < (Retained N 12 F).card := by
  have hb := retained_near hN hF hcard
  have hn : (291012 : ℝ) ≤ N := by exact_mod_cast hN
  have hp := mul_pos (show (0 : ℝ) < (N : ℝ)-5256 by linarith only [hn])
    (show (0 : ℝ) < N by linarith only [hn])
  nlinarith only [hb, hp]

theorem actual_retained_card_two {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 291012≤N) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    2≤(Retained N 12 F).card := by
  have hb := actual_retained_above_cross_gap hN hF hcard
  have hn : (2 : ℝ)≤N := by exact_mod_cast (show 2≤N by omega)
  by_contra hh
  have hc : ((Retained N 12 F).card : ℝ)≤1 := by
    exact_mod_cast (by omega : (Retained N 12 F).card≤1)
  have hp := mul_nonneg (show (0 : ℝ)≤(N : ℝ)-2 by linarith only [hn])
    (show (0 : ℝ)≤(N : ℝ)+2 by positivity)
  nlinarith only [hp,hb,hc]

theorem actual_initial_preparation {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 291012≤N) (hhigh : N≤642498)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hcommon : ∃c∈Ground N,∀S∈Retained N 12 F,¬IsAP S→c∈S) :
    F.card≤B N ∨ ∃H : Finset (Finset ℤ),∃c L R : ℕ,∃P T : Finset ℤ,
      (H=F ∨ H=Family N F) ∧ H.card=F.card ∧ RootModel291012.Start N c L R H P T := by
  obtain ⟨c,hc,hroot⟩ := hcommon
  have hG := actual_retained_legal (r := 12) hF
  have hcase := actual_near_one_sided_reduction hN hhigh hc hG hroot
    (actual_retained_above_cross_gap hN hF hcard)
  obtain ⟨H,hHF,hLH,hcardH,_hD,_hG,d,hd,hrootH,hcaseH⟩ :=
    actual_retained_right_orientation N 12 F c hF hc hroot hcase
  have hnearH : B N≤H.card := by omega
  rcases hcaseH with hstar | hright
  · have hb := StarStart291012.actual_retained_star_window hN (by omega : N≤642498)
      hd hLH hstar
    exact Or.inl (by omega)
  · have htwo := actual_retained_card_two hN hLH hnearH
    obtain ⟨L,R,hLc,hLR,hRN,hP,hT,henv⟩ := actual_outside_member_envelope
      (actual_retained_legal hLH) htwo hright
    have hddata := (mem_ground N d).mp hd
    let c' := d.toNat
    have hcast : (c' : ℤ)=d := by dsimp only [c'];omega
    have hc' : (c' : ℤ)∈Ground N := by rwa [hcast]
    have hcL : c'<L := by omega
    have hroot' : ∀S∈Retained N 12 H,¬IsAP S→(c' : ℤ)∈S := by
      simpa only [hcast] using hrootH
    obtain ⟨P,hPG,hLP⟩ := hP
    obtain ⟨T,hTG,hTR⟩ := hT
    have hPF := (Finset.mem_filter.mp hPG).1
    have hcP : (c' : ℤ)∉P := by simpa only [hcast] using (Finset.mem_filter.mp hPG).2
    have hTF := (Finset.mem_filter.mp hTG).1
    have hcT : (c' : ℤ)∉T := by simpa only [hcast] using (Finset.mem_filter.mp hTG).2
    have houtside : ∀S∈Retained N 12 H,(c' : ℤ)∉S→
        (∃u∈S,u≤(L : ℤ)) ∧ ∃v∈S,(R : ℤ)≤v := by
      intro S hS hcS
      have hSG : S∈Avoiders (Retained N 12 H) d :=
        Finset.mem_filter.mpr ⟨hS,by simpa only [←hcast] using hcS⟩
      obtain ⟨⟨a,ha,haL,_haMin⟩,b,hb,hRb,_hbMax⟩ := henv S hSG
      exact ⟨⟨a,ha,haL⟩,b,hb,hRb⟩
    exact Or.inr ⟨H,c',L,R,P,T,hHF,hcardH,
      ⟨hc',hLH,hnearH,hcL,hLR,hRN,hroot',hPF,hcP,hLP,hTF,hcT,hTR,houtside⟩⟩


#print axioms retained_near
#print axioms actual_retained_above_cross_gap
#print axioms actual_retained_card_two
#print axioms actual_initial_preparation
end
end JSP233.InitialPreparation291012
