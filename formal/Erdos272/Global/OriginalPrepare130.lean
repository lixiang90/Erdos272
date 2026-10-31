import Erdos272.Arithmetic.RawLogGate130
import Erdos272.Resources.CoarseEndpoint130
import Erdos272.Arithmetic.PreparationScales119
import Erdos272.Retention.RestoreDense120
import Erdos272.Retention.Restore11Ratio113
import Erdos272.Global.NonInterval113
import Erdos272.Counting.OneSided47
import Erdos272.Global.NonInterval53

/-! Round129: same-family recovery from the direct fifteen-term moment. -/
namespace JSP233.OriginalPrepare130
open StarCompletion APGeometry DenseDeletion40 DenseSharper41 FamilyReflect43
open LinearOmitters43 OutsideEnvelope43 OneSided47 Straddling47 APCount41
open HarmonicAbel29 LongTerminal35 RawEndpoint112 RawLogGate130
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_log_gates {N : ℕ} (hN : 107277000≤N) (hNu : N<2^49) :
    let J := Nat.log 2 N+1
    27≤J ∧ J≤49 ∧ N<2^J ∧ 1024*J^3≤N ∧ 468*J^3≤N :=
  PreparationScales119.actual_log_gates (by omega : 74320000≤N) hNu


theorem actual_retained_near11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 107277000≤N) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    (N:ℝ)^2/2≤(Retained N 11 F).card+486*(N:ℝ) := by
  have hd := actual_retained_sharp_lower (r:=11) (by decide : 0<11)
    (by norm_num;omega) hF
  have hdR : (F.card:ℝ)≤(Retained N 11 F).card+485*(N:ℝ) := by exact_mod_cast hd
  have hb : N.choose 2+1≤F.card := by unfold B at hcard;omega
  have hbR : (N:ℝ)*((N:ℝ)-1)/2+1≤F.card := by
    have hh : (N.choose 2:ℝ)+1≤F.card := by exact_mod_cast hb
    simpa only [Nat.cast_choose_two] using hh
  have hn : (0:ℝ)≤N := Nat.cast_nonneg N
  nlinarith only [hdR,hbR,hn]

theorem actual_retained_above_cross_gap11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 107277000≤N) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    17*(N:ℝ)^2/36<(Retained N 11 F).card := by
  have hb := actual_retained_near11 hN hF hcard
  have hn : (107277000:ℝ)≤N := by exact_mod_cast hN
  have hp := mul_pos (show (0:ℝ)<(N:ℝ)-17496 by linarith only [hn])
    (show (0:ℝ)<N by linarith only [hn])
  nlinarith only [hp,hb]

theorem actual_retained_card_two11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 107277000≤N) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    2≤(Retained N 11 F).card := by
  have hb := actual_retained_above_cross_gap11 hN hF hcard
  have hn : (2:ℝ)≤N := by exact_mod_cast (show 2≤N by omega)
  by_contra hh
  have hc : ((Retained N 11 F).card:ℝ)≤1 := by
    exact_mod_cast (by omega : (Retained N 11 F).card≤1)
  have hp := mul_nonneg (show (0:ℝ)≤(N:ℝ)-2 by linarith only [hn])
    (show (0:ℝ)≤(N:ℝ)+2 by positivity)
  nlinarith only [hp,hb,hc]

theorem actual_two_step_straddling_gap {N J : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 1≤N) (hJ : 4≤J) (hNJ : N<2^J) (hscale : 468*J^3≤N)
    (hcN : c∈Ground N) (hF : Legal (Ground N) F)
    (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hcross : ∀S∈F,c∉S→StraddlesRoot c S)
    (hno : ¬LargeStepAvoider F c) (hout : ∃P∈F,c∉P) :
    (F.card:ℝ)≤17*(N:ℝ)^2/36 := by
  have hJR : (4:ℝ)≤J := by exact_mod_cast hJ
  have hH := HarmonicSharp39.actual_harmonic_tight N J hNJ
  have hH0 := harmonic_nonneg N
  have hHJ : Harmonic N≤J := by linarith only [hH,hJR]
  have hH3 : Harmonic N^3≤(J:ℝ)^3 := by gcongr
  have hJ3 : (1:ℝ)≤(J:ℝ)^3 := by
    have hp := mul_nonneg (show (0:ℝ)≤(J:ℝ)-1 by linarith only [hJR])
      (show (0:ℝ)≤(J:ℝ)^2+J+1 by positivity)
    nlinarith only [hp]
  have hb := OneSided47.actual_two_step_straddling_count hcN hF hroot hcross hno hout
  have hlin := mul_le_mul_of_nonneg_left hJ3 (Nat.cast_nonneg (α:=ℝ) N)
  have hcube := mul_le_mul_of_nonneg_left hH3 (show (0:ℝ)≤6*(N:ℝ) by positivity)
  have hs : (468:ℝ)*(J:ℝ)^3≤N := by exact_mod_cast hscale
  have hsN := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α:=ℝ) N)
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hunit : (1:ℝ)≤(N:ℝ)*(J:ℝ)^3 := by nlinarith only [hlin,hn]
  nlinarith only [hb,hlin,hcube,hsN,hunit]

theorem actual_all_cross_root_gap {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 107277000≤N) (hNu : N<2^49) (hcN : c∈Ground N)
    (hF : Legal (Ground N) F) (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hcross : ∀S∈F,c∉S→StraddlesRoot c S) (hout : ∃P∈F,c∉P) :
    (F.card:ℝ)≤17*(N:ℝ)^2/36 := by
  let J := Nat.log 2 N+1
  obtain ⟨hJl,_hJu,hNJ,_hbig,hscale⟩ := actual_log_gates hN hNu
  by_cases hlarge : LargeStepAvoider F c
  · obtain ⟨P,hP,hcP,d,hd,p,hAP⟩ := hlarge
    exact NonIntervalAP47.actual_large_step_straddling_gap
      (by omega : 6≤N) hNJ hscale hcN hF hroot hcross hP hcP (by exact_mod_cast hd) hAP
  · exact actual_two_step_straddling_gap (by omega : 1≤N) (by omega : 4≤J)
      hNJ hscale hcN hF hroot hcross hlarge hout

theorem actual_near_one_sided_reduction {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 107277000≤N) (hNu : N<2^49) (hcN : c∈Ground N)
    (hF : Legal (Ground N) F) (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hnear : 17*(N:ℝ)^2/36<F.card) :
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
    have hb := actual_all_cross_root_gap hN hNu hcN hF hroot hcross hout
    linarith only [hb,hnear]

theorem actual_original_upper_of_root11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 107277000≤N) (hNu : N<2^49) (hF : Legal (Ground N) F)
    (hcommon : ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S) : F.card≤B N := by
  by_contra hno
  have hcounter : B N<F.card := by omega
  have hcard : B N≤F.card := hcounter.le
  obtain ⟨c,hc,hroot⟩ := hcommon
  have hG := actual_retained_legal (r:=11) hF
  have hcase := actual_near_one_sided_reduction hN hNu hc hG hroot
    (actual_retained_above_cross_gap11 hN hF hcard)
  obtain ⟨H,_hHF,hLH,hHF,_hD,hGcard,d,hd,hrootH,hcaseH⟩ :=
    actual_retained_right_orientation N 11 F c hF hc hroot hcase
  have hcardH : B N≤H.card := by omega
  rcases hcaseH with hstar | hright
  · have hb := actual_retained_star_original_payment (r:=11) (by decide : 0<11)
      (by norm_num;omega) (by norm_num;omega) hd hLH hstar
    omega
  · have htwo : 2≤(Retained N 11 H).card := actual_retained_card_two11 hN hLH hcardH
    obtain ⟨L,R,hLc,hLR,hRN,hP,hT,henv⟩ := actual_outside_member_envelope
      (actual_retained_legal hLH) htwo hright
    have hddata := (mem_ground N d).mp hd
    let c' := d.toNat
    have hcast : (c':ℤ)=d := by dsimp only [c'];omega
    have hc' : (c':ℤ)∈Ground N := by rwa [hcast]
    have hc1 : 1≤c' := by omega
    have hcL : c'<L := by omega
    have hroot' : ∀S∈Retained N 11 H,¬IsAP S→(c':ℤ)∈S := by simpa only [hcast] using hrootH
    obtain ⟨P,hPG,hLP⟩ := hP
    obtain ⟨T,hTG,hTR⟩ := hT
    have hPF := (Finset.mem_filter.mp hPG).1
    have hcP : (c':ℤ)∉P := by simpa only [hcast] using (Finset.mem_filter.mp hPG).2
    have hTF := (Finset.mem_filter.mp hTG).1
    have hcT : (c':ℤ)∉T := by simpa only [hcast] using (Finset.mem_filter.mp hTG).2
    have houtside : ∀S∈Retained N 11 H,(c':ℤ)∉S→
        (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v := by
      intro S hS hcS
      have hSG : S∈Avoiders (Retained N 11 H) d :=
        Finset.mem_filter.mpr ⟨hS,by simpa only [←hcast] using hcS⟩
      obtain ⟨⟨a,ha,haL,_haMin⟩,b,hb,hRb,_hbMax⟩ := henv S hSG
      exact ⟨⟨a,ha,haL⟩,b,hb,hRb⟩
    have hwCoarse := CoarseEndpoint130.actual_retained11_width (by omega : 100000≤N) hc' hLH hcardH
      hcL hLR hRN hroot' hPF hcP hLP hTF hcT hTR houtside
    have he : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N-R) := by
      rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add]
      ring
    have hwCoarseNat : ((L+N-R:ℕ):ℝ)^2≤(N:ℝ)*CoarseEndpoint130.CoarsePolynomial (Real.log N) := by
      rwa [he]
    have hthin := actual_preliminary_width_payment hN hwCoarseNat
    have hscale : 32*L≤N := by omega
    obtain ⟨_hJl,_hJu,hNJ,hJcube,_h468⟩ := actual_log_gates hN hNu
    have hlow : ∀S∈Avoiders (Retained N 11 H) (c':ℤ),∃a∈S,a≤(L:ℤ) := by
      intro S hS
      exact (houtside S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2).1
    have hright' : ∀S∈Avoiders (Retained N 11 H) (c':ℤ),∃b∈S,(R:ℤ)≤b := by
      intro S hS
      exact (houtside S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2).2
    have hi := NonInterval113.actual_avoiders_intervals (δ:=486)
      (by omega : 6≤N) hNJ hc' (actual_retained_legal hLH) hroot' hcL hLR hRN hlow hright'
      hscale hJcube (by omega : 24*486<N) (actual_retained_near11 hN hLH hcardH)
    have hne : (Avoiders (Retained N 11 H) (c':ℤ)).Nonempty :=
      ⟨P,Finset.mem_filter.mpr ⟨hPF,hcP⟩⟩
    by_cases hsmall : L+N-R≤90
    · have hpaySmall : 1120*(L+N-R)≤23*N := by omega
      have hb := Restore11Ratio113.actual_deleted_avoider_restore11_ratio N c' L R H
        (hNu.trans (by norm_num : (2:ℕ)^49<2^50)) (by omega : 26000≤N)
        hc1 hcL hLR hRN hpaySmall hLH hne hi
      omega
    · have hlarge : 90<L+N-R := by omega
      have hw := RawEndpoint130.actual_readded11_bootstrap_width (by omega : 100000≤N)
        hc' hLH hcardH hcL hLR hRN hroot' hPF hcP hLP hTF hcT hTR houtside hi hthin
      have hwNat : ((L+N-R:ℕ):ℝ)^2≤(N:ℝ)*RawEndpoint130.BootstrapPolynomial (Real.log N) := by
        rwa [he]
      have hpay := actual_balanced_width_payment hN hwNat
      have hprofile := RawEndpoint130.actual_readded11_bootstrap_profile_width
        (by omega : 100000≤N) hc' hLH hcardH hcL hLR hRN hroot'
        hPF hcP hLP hTF hcT hTR houtside hi hthin
      have hprofileNat : RawEndpoint115.ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
          (N:ℝ)*RawEndpoint130.BootstrapCorePolynomial (Real.log N) := by
        simpa only [Nat.cast_sub hRN] using hprofile
      have hnorm := actual_bootstrap_profile_payment hN hprofileNat
      have hD : RawEndpoint115.ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
          RawEndpoint112.DeficitCoeff/(900/23:ℝ)^2*(N:ℝ)^2 := by
        dsimp only [RawEndpoint112.DeficitCoeff] at hnorm ⊢
        nlinarith only [hnorm]
      have hb := RestoreDense120.actual_deleted_avoider_restore11_profile900 N c' L R H
        (hNu.trans (by norm_num : (2:ℕ)^49<2^50)) (by omega : 2000000≤N)
        hc1 hcL hLR hRN hpay hD hlarge hLH hne hi
      omega

#print axioms actual_log_gates
#print axioms actual_retained_near11
#print axioms actual_retained_above_cross_gap11
#print axioms actual_retained_card_two11
#print axioms actual_two_step_straddling_gap
#print axioms actual_all_cross_root_gap
#print axioms actual_near_one_sided_reduction
#print axioms actual_original_upper_of_root11
end
end JSP233.OriginalPrepare130
