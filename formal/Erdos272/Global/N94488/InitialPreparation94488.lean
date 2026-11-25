module

public import Erdos272.Global.N109474.InitialPreparation109474
public import Erdos272.Global.N109474.CrossGap109474
public import Erdos272.Global.N94488.StarStart94488
public import Erdos272.Resources.RetainedIntervals213

@[expose] public section

namespace JSP233.InitialPreparation94488
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29
open FamilyReflect43 OutsideEnvelope43 Reflect37 WitnessInterval43 RetainedIntervals213 CrossGap109474
open InitialPreparation109474
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_initial_preparation {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 94488≤N) (hhigh : N≤179999)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hcommon : ∃c∈Ground N,∀S∈Retained N 12 F,¬IsAP S→c∈S) :
    F.card≤B N ∨ ∃H : Finset (Finset ℤ),∃c L R : ℕ,∃P T : Finset ℤ,
      (H=F ∨ H=Family N F) ∧ H.card=F.card ∧ RootModel291012.Start N c L R H P T := by
  obtain ⟨c,hc,hroot⟩ := hcommon
  have hG := actual_retained_legal (r := 12) hF
  have hcase := actual_near_one_sided_reduction (by omega : 61920≤N) hhigh hc hG hroot
    (actual_retained_above_cross_gap (by omega : 15853≤N) hF hcard)
  obtain ⟨H,hHF,hLH,hcardH,_hD,_hG,d,hd,hrootH,hcaseH⟩ :=
    actual_retained_right_orientation N 12 F c hF hc hroot hcase
  have hnearH : B N≤H.card := by omega
  rcases hcaseH with hstar | hright
  · have hb := StarStart94488.actual_retained_star_window hN (by omega : N≤179999)
      hd hLH hstar
    exact Or.inl (by omega)
  · have htwo := actual_retained_card_two (by omega : 15853≤N) hLH hnearH
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


#print axioms actual_initial_preparation
end
end JSP233.InitialPreparation94488
