import Erdos272.Resources.RetainedIntervals208
import Erdos272.Resources.StarWindow208
import Erdos272.Counting.OneSided47

/-! Actual startup from a common retained crooked root.  The all-cross case
is excluded with the finite harmonic cap before choosing physical endpoints.
The rooted case pays the original family directly; reflection preserves the
original cardinality in the remaining case. -/
namespace JSP233.InitialPreparation208
open StarCompletion APGeometry DenseDeletion40 FamilyReflect43 OutsideEnvelope43
open OneSided47 Straddling47 APCount41 HarmonicAbel29
open ActualRecoveryChain208 RecoveryPrefix208 RetainedIntervals208 LocalResourceRecovery208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_all_cross_root_gap {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 659912≤N) (hhigh : N≤705097) (hc : c∈Ground N)
    (hF : Legal (Ground N) F) (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hcross : ∀S∈F,c∉S→StraddlesRoot c S) (hout : ∃P∈F,c∉P) :
    (F.card : ℝ)≤17*(N : ℝ)^2/36 := by
  have hn : (659912 : ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hn1 : (1 : ℝ)≤N := by linarith only [hn]
  have hH := harmonic_cap (by omega : 100000≤N) hhigh
  have hH141 : Harmonic N≤(141/10 : ℝ) := hH.trans (by norm_num [HCap])
  have hH0 := harmonic_nonneg N
  have hH3 : Harmonic N^3≤(141/10 : ℝ)^3 := by gcongr
  have hcube := mul_le_mul_of_nonneg_left hH3 (show (0 : ℝ)≤6*N by positivity)
  by_cases hlarge : LargeStepAvoider F c
  · obtain ⟨P,hP,hcP,d,hd,p,hAP⟩ := hlarge
    have hb := NonIntervalAP47.actual_large_step_straddling_count
      (by omega : 6≤N) hc hF hroot hcross hP hcP (by exact_mod_cast hd) hAP
    have hlin := mul_le_mul_of_nonneg_left hH141 hn0
    have hgate : 6*(141/10 : ℝ)^3+141/10+6≤(N : ℝ)/36 := by
      linarith only [hn]
    have hpaid := mul_le_mul_of_nonneg_right hgate hn0
    nlinarith only [hb,hlin,hcube,hpaid]
  · have hb := OneSided47.actual_two_step_straddling_count hc hF hroot hcross hlarge hout
    have hgate : 6*(141/10 : ℝ)^3+4≤(5/144 : ℝ)*N := by linarith only [hn]
    have hpaid := mul_le_mul_of_nonneg_right hgate hn0
    nlinarith only [hb,hcube,hpaid,hn1]

theorem actual_near_one_sided_reduction {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 659912≤N) (hhigh : N≤705097) (hc : c∈Ground N)
    (hF : Legal (Ground N) F) (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hnear : 17*(N : ℝ)^2/36<F.card) :
    Rooted F c ∨ ∃P∈F,c∉P ∧ ((∀x∈P,x<c) ∨ ∀x∈P,c<x) := by
  by_cases hr : Rooted F c
  · exact Or.inl hr
  · apply Or.inr
    by_contra hn
    have hcross := actual_no_one_sided_cross hn
    have hout : ∃P∈F,c∉P := by
      change ¬∀P∈F,c∈P at hr
      push Not at hr
      exact hr
    have hb := actual_all_cross_root_gap hN hhigh hc hF hroot hcross hout
    linarith only [hb,hnear]

theorem actual_retained_above_cross_gap11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    17*(N : ℝ)^2/36<(Retained N 11 F).card := by
  have hb := DenseDeletion208.actual_retained11_near (by omega : 10902≤N) hF hcard
  have hn : (659912 : ℝ)≤N := by exact_mod_cast hN
  have hp := mul_pos (show (0 : ℝ)<(N : ℝ)-4428 by linarith only [hn])
    (show (0 : ℝ)<N by linarith only [hn])
  nlinarith only [hp,hb]

theorem actual_retained_card_two11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    2≤(Retained N 11 F).card := by
  have hb := actual_retained_above_cross_gap11 hN hF hcard
  have hn : (2 : ℝ)≤N := by exact_mod_cast (show 2≤N by omega)
  by_contra hh
  have hc : ((Retained N 11 F).card : ℝ)≤1 := by
    exact_mod_cast (by omega : (Retained N 11 F).card≤1)
  have hp := mul_nonneg (show (0 : ℝ)≤(N : ℝ)-2 by linarith only [hn])
    (show (0 : ℝ)≤(N : ℝ)+2 by positivity)
  nlinarith only [hp,hb,hc]

theorem actual_initial_preparation {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhigh : N≤705097)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hcommon : ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S) :
    F.card≤B N ∨ ∃H : Finset (Finset ℤ),∃c L R : ℕ,∃P T : Finset ℤ,
      (H=F ∨ H=Family N F) ∧ H.card=F.card ∧ InitialGeometry N c L R H P T := by
  obtain ⟨c,hc,hroot⟩ := hcommon
  have hG := actual_retained_legal (r := 11) hF
  have hcase := actual_near_one_sided_reduction hN hhigh hc hG hroot
    (actual_retained_above_cross_gap11 hN hF hcard)
  obtain ⟨H,hHF,hLH,hcardH,_hD,_hG,d,hd,hrootH,hcaseH⟩ :=
    actual_retained_right_orientation N 11 F c hF hc hroot hcase
  have hnearH : B N≤H.card := by omega
  rcases hcaseH with hstar | hright
  · have hb := StarWindow208.actual_retained_star_window hN (by omega : N≤62443451)
      hd hLH hstar
    exact Or.inl (by omega)
  · have htwo := actual_retained_card_two11 hN hLH hnearH
    obtain ⟨L,R,hLc,hLR,hRN,hP,hT,henv⟩ := actual_outside_member_envelope
      (actual_retained_legal hLH) htwo hright
    have hddata := (mem_ground N d).mp hd
    let c' := d.toNat
    have hcast : (c' : ℤ)=d := by dsimp only [c'];omega
    have hc' : (c' : ℤ)∈Ground N := by rwa [hcast]
    have hcL : c'<L := by omega
    have hroot' : ∀S∈Retained N 11 H,¬IsAP S→(c' : ℤ)∈S := by
      simpa only [hcast] using hrootH
    obtain ⟨P,hPG,hLP⟩ := hP
    obtain ⟨T,hTG,hTR⟩ := hT
    have hPF := (Finset.mem_filter.mp hPG).1
    have hcP : (c' : ℤ)∉P := by simpa only [hcast] using (Finset.mem_filter.mp hPG).2
    have hTF := (Finset.mem_filter.mp hTG).1
    have hcT : (c' : ℤ)∉T := by simpa only [hcast] using (Finset.mem_filter.mp hTG).2
    have houtside : ∀S∈Retained N 11 H,(c' : ℤ)∉S→
        (∃u∈S,u≤(L : ℤ)) ∧ ∃v∈S,(R : ℤ)≤v := by
      intro S hS hcS
      have hSG : S∈Avoiders (Retained N 11 H) d :=
        Finset.mem_filter.mpr ⟨hS,by simpa only [←hcast] using hcS⟩
      obtain ⟨⟨a,ha,haL,_haMin⟩,b,hb,hRb,_hbMax⟩ := henv S hSG
      exact ⟨⟨a,ha,haL⟩,b,hb,hRb⟩
    exact Or.inr ⟨H,c',L,R,P,T,hHF,hcardH,
      ⟨hN,hhigh,hc',hLH,hnearH,hcL,hLR,hRN,hroot',hPF,hcP,hLP,hTF,hcT,hTR,houtside⟩⟩

theorem actual_original_upper_of_root11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F)
    (hcommon : ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S)
    (hi : TotientInputs N) : F.card≤B N := by
  by_cases hcard : B N≤F.card
  · rcases actual_initial_preparation hN hhigh hF hcard hcommon with hb |
      ⟨H,c,L,R,P,T,_hHF,hcardH,g⟩
    · exact hb
    · have hb := RetainedIntervals208.actual_recovered_original g hi
      omega
  · omega

#print axioms actual_all_cross_root_gap
#print axioms actual_near_one_sided_reduction
#print axioms actual_retained_above_cross_gap11
#print axioms actual_initial_preparation
#print axioms actual_original_upper_of_root11
end
end JSP233.InitialPreparation208
