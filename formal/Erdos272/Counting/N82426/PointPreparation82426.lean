module

public import Erdos272.Arithmetic.N94488.HarmonicCaps94488
public import Erdos272.Counting.N86412.StarClasses86412
public import Erdos272.Counting.N86412.DenseCount86412
public import Erdos272.Global.N109474.InitialPreparation109474
public import Erdos272.Global.N109474.CrossGap109474
public import Erdos272.Resources.RetainedIntervals213

@[expose] public section

namespace JSP233.PointPreparation82426
open StarCompletion StarResources30 CrossLine30 JointResources31 HarmonicAbel29 DenseDeletion40
open LowSteps32 APGeometry RecoveryCaps213 StarClasses86412
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem actual_small_kernel_window {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hN : 82426 ≤ N) (hhi : N ≤ 179999) (hc : c ∈ Ground N) (hF : Legal (Ground N) F)
    (htwo : 2 ≤ (Avoiders F c).card) (hkernel : (CommonKernel (Ground N) F c).card ≤ 1)
    (hcount : (Avoiders F c).card ≤ 81*N) : F.card ≤ B N := by
  by_contra hn
  have hcounter : N.choose 2+1 ≤ F.card := by unfold B at hn; omega
  have hlow := StarWindow212.actual_AP_lower (by omega : 65536 ≤ N) hc hF htwo hkernel hcounter
  let A := APLarge (RootPart F c)
  have hground : ∀ S ∈ A, S ⊆ Ground N := fun S hS =>
    hF.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hAP : ∀ S ∈ A, IsAP S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have hroot : Rooted A c := fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hlarge : ∀ S ∈ A, 4 ≤ S.card := fun S hS => (Finset.mem_filter.mp hS).2.2
  have htotal := StarClasses86412.actual_AP_total N c A hground hAP hroot hlarge hc
  change (A.card : ℝ) ≤ (∑ d ∈ LowActiveEight c A,
    ((StepClass A (trueStep c) (d : ℤ)).card : ℝ))+
      ((N-1 : ℕ) : ℝ)^2/32+2*((N-1 : ℕ) : ℝ)*Harmonic (N-1)+((N-1 : ℕ) : ℝ) at htotal
  have hh : Harmonic (N-1) ≤ 14 := (harmonic_mono (Nat.sub_le N 1)).trans
    ((HarmonicCaps94488.source_cap hhi).trans (by norm_num))
  have hHpay := mul_le_mul_of_nonneg_left hh
    (show (0 : ℝ) ≤ 2*((N-1 : ℕ) : ℝ) by positivity)
  have hb := StarClasses86412.actual_budget_with_low_surpluses hc hF
  have hcountR : ((Avoiders F c).card : ℝ) ≤ 81*((N-1 : ℕ) : ℝ)+81 := by
    have hx : ((Avoiders F c).card : ℝ) ≤ 81*(N : ℝ) := by exact_mod_cast hcount
    have he : (N : ℝ) = ((N-1 : ℕ) : ℝ)+1 := by exact_mod_cast (show N = N-1+1 by omega)
    linarith only [hx, he]
  have hkR : ((CommonKernel (Ground N) F c).card : ℝ) ≤ 1 := by exact_mod_cast hkernel
  have hcounterR : ((N-1).choose 2 : ℝ)+((N-1 : ℕ) : ℝ)+1 ≤ F.card := by
    have hid := StarBudget30.small_budget_identity N (by omega : 1 ≤ N)
    have hx : (N.choose 2 : ℝ)+1 ≤ F.card := by exact_mod_cast hcounter
    have hi : (N.choose 2 : ℝ)+1 = (N : ℝ)+((N-1).choose 2 : ℝ) := by exact_mod_cast hid.symm
    have he : (N : ℝ) = ((N-1 : ℕ) : ℝ)+1 := by exact_mod_cast (show N = N-1+1 by omega)
    linarith only [hx, hi, he]
  have hnR : (82425 : ℝ) ≤ ((N-1 : ℕ) : ℝ) := by exact_mod_cast (show 82425 ≤ N-1 by omega)
  have hp := mul_nonneg (show (0 : ℝ) ≤ ((N-1 : ℕ) : ℝ)-82425 by linarith only [hnR])
    (show (0 : ℝ) ≤ ((N-1 : ℕ) : ℝ) by positivity)
  change (((N-1 : ℕ) : ℝ)^2/18)-(7/2 : ℝ)*((N-1 : ℕ) : ℝ)-2*(Avoiders F c).card+1 ≤ A.card at hlow
  change (F.card : ℝ)+((∑ d ∈ LowActiveEight c A,
    ((StepClass A (trueStep c) (d : ℤ)).card : ℝ))-8000000)/21 ≤ _ at hb
  nlinarith only [hlow, htotal, hHpay, hb, hcountR, hkR, hcounterR, hp, hnR]

#print axioms actual_small_kernel_window
end
end JSP233.PointPreparation82426

namespace JSP233.PointPreparation82426
open StarCompletion APGeometry DenseDeletion40
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 864120
theorem actual_retained_star_window {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hN : 82426≤N) (hhi : N≤179999)
    (hc : c∈Ground N) (hF : Legal (Ground N) F)
    (hroot : Rooted (Retained N 12 F) c) : F.card≤B N := by
  have hsub : Avoiders F c⊆Deleted N 12 F := by
    intro S hS
    obtain ⟨hSF,hcS⟩ := Finset.mem_filter.mp hS
    by_contra hnd
    exact hcS (hroot S (Finset.mem_sdiff.mpr ⟨hSF,hnd⟩))
  have hbad : ∀S∈Avoiders F c,¬IsAP S :=
    fun S hS => (Finset.mem_filter.mp (hsub hS)).2.1
  have hdel := DenseCount86412.actual_deleted_count (by omega : 56400≤N) (by omega : N ≤ 2^18) hF
  have hcount : (Avoiders F c).card≤81*N := (Finset.card_le_card hsub).trans hdel
  by_cases htwo : 2≤(Avoiders F c).card
  · by_cases hk : 2≤(CommonKernel (Ground N) F c).card
    · have hb := AnchorCompletion38.actual_crooked_large_kernel_payment N F c hc hF htwo hk hbad
      omega
    · exact PointPreparation82426.actual_small_kernel_window (by omega : 82426≤N) hhi hc hF htwo (by omega) hcount
  · apply AnchorCompletion38.actual_crooked_omitter_middle_window N F c (by omega) hc hF hbad
    omega


#print axioms actual_retained_star_window
end
end JSP233.PointPreparation82426

namespace JSP233.PointPreparation82426
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29
open FamilyReflect43 OutsideEnvelope43 Reflect37 WitnessInterval43 RetainedIntervals213 CrossGap109474
open InitialPreparation109474
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_initial_preparation {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 82426≤N) (hhigh : N≤179999)
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
  · have hb := PointPreparation82426.actual_retained_star_window hN (by omega : N≤179999)
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
end JSP233.PointPreparation82426
