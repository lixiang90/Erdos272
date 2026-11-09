module

public import Erdos272.Resources.LocalReduction136
public import Erdos272.Resources.HalfRecovery133

@[expose] public section
namespace JSP233.HalfRecovery136
open StarCompletion APGeometry CoprimeDensity52 MiddleJoint51 MiddleDeficit52
open PreparedClasses50 APPrepare49 PreparedWitness48 MiddleCoordinates51
open DenseDeletion40 DenseSharper41 FamilyReflect43 RestrictedWitness44 LongTerminal35
open LinearOmitters43 OutsideEnvelope43 OneSided47 Straddling47 APCount41
open HarmonicAbel29 HarmonicLog55 RawEndpoint112 RawEndpoint115 PairRecovery131 HalfRecovery133
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_original_upper_of_root11 {N : ℕ} {C : ℝ} {F : Finset (Finset ℤ)}
    (hN : 71425022≤N) (hhi : N≤73791522) (hNu : N<2^49) (hF : Legal (Ground N) F)
    (cert : HalfConstantCertificate N C)
    (hcommon : ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S) : F.card≤B N := by
  obtain ⟨hbudget,hcoarse,hfine⟩ := cert
  by_contra hno
  have hcounter : B N<F.card := by omega
  have hcard : B N≤F.card := hcounter.le
  obtain ⟨c,hc,hroot⟩ := hcommon
  have hG := actual_retained_legal (r:=11) hF
  have hcase := LocalReduction136.actual_near_one_sided_reduction hN hhi hc hG hroot
    (LocalReduction136.actual_retained_above_cross_gap11 hN hF hcard)
  obtain ⟨H,_hHF,hLH,hHF,_hD,hGcard,d,hd,hrootH,hcaseH⟩ :=
    actual_retained_right_orientation N 11 F c hF hc hroot hcase
  have hcardH : B N≤H.card := by omega
  rcases hcaseH with hstar | hright
  · have hb := actual_retained_star_original_payment (r:=11) (by decide : 0<11)
      (by norm_num;omega) (by norm_num;omega) hd hLH hstar
    omega
  · have htwo : 2≤(Retained N 11 H).card := LocalReduction136.actual_retained_card_two11 hN hLH hcardH
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
    have hwCoarse := HalfRecovery133.actual_retained11_width (by omega : 100000≤N) hc' hLH hcardH
      hcL hLR hRN hroot' hPF hcP hLP hTF hcT hTR houtside (hbudget _ hc')
    have he : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N-R) := by
      rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add]
      ring
    have hwCoarseNat : ((L+N-R:ℕ):ℝ)^2≤(N:ℝ)*(Rho*(C+9677/20)) := by
      rwa [he]
    have hthin := actual_preliminary_width_payment hcoarse hwCoarseNat
    have hscale : 32*L≤N := by omega
    obtain ⟨_hJl,_hJu,hNJ,hJcube,_h468⟩ := LocalReduction136.actual_log_gates hN hhi
    have hlow : ∀S∈Avoiders (Retained N 11 H) (c':ℤ),∃a∈S,a≤(L:ℤ) := by
      intro S hS
      exact (houtside S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2).1
    have hright' : ∀S∈Avoiders (Retained N 11 H) (c':ℤ),∃b∈S,(R:ℤ)≤b := by
      intro S hS
      exact (houtside S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2).2
    have hi := NonInterval113.actual_avoiders_intervals (δ:=486)
      (by omega : 6≤N) hNJ hc' (actual_retained_legal hLH) hroot' hcL hLR hRN hlow hright'
      hscale hJcube (by omega : 24*486<N) (LocalReduction136.actual_retained_near11 hN hLH hcardH)
    have hne : (Avoiders (Retained N 11 H) (c':ℤ)).Nonempty :=
      ⟨P,Finset.mem_filter.mpr ⟨hPF,hcP⟩⟩
    by_cases hsmall : L+N-R≤90
    · have hpaySmall : 1120*(L+N-R)≤23*N := by omega
      have hb := Restore11Ratio113.actual_deleted_avoider_restore11_ratio N c' L R H
        (hNu.trans (by norm_num : (2:ℕ)^49<2^50)) (by omega : 26000≤N)
        hc1 hcL hLR hRN hpaySmall hLH hne hi
      omega
    · have hlarge : 90<L+N-R := by omega
      have hw := HalfRecovery133.actual_readded11_bootstrap_width (by omega : 100000≤N)
        hc' hLH hcardH hcL hLR hRN hroot' hPF hcP hLP hTF hcT hTR houtside hi hthin (hbudget _ hc')
      have hwNat : ((L+N-R:ℕ):ℝ)^2≤(N:ℝ)*(Rho*C) := by
        rwa [he]
      have hpay := actual_balanced_width_payment hfine hwNat
      have hprofile := HalfRecovery133.actual_readded11_bootstrap_profile_width
        (by omega : 100000≤N) hc' hLH hcardH hcL hLR hRN hroot'
        hPF hcP hLP hTF hcT hTR houtside hi hthin (hbudget _ hc')
      have hprofileNat : RawEndpoint115.ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
          (N:ℝ)*C := by
        simpa only [Nat.cast_sub hRN] using hprofile
      have hnorm := actual_bootstrap_profile_payment hfine hprofileNat
      have hD : RawEndpoint115.ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
          RawEndpoint112.DeficitCoeff/(900/23:ℝ)^2*(N:ℝ)^2 := by
        dsimp only [RawEndpoint112.DeficitCoeff] at hnorm ⊢
        nlinarith only [hnorm]
      have hb := RestoreDense120.actual_deleted_avoider_restore11_profile900 N c' L R H
        (hNu.trans (by norm_num : (2:ℕ)^49<2^50)) (by omega : 2000000≤N)
        hc1 hcL hLR hRN hpay hD hlarge hLH hne hi
      omega

theorem actual_original_upper_of_certificate {N : ℕ} {C : ℝ} {F : Finset (Finset ℤ)}
    (hN : 71425022≤N) (hhi : N≤73791522) (hNu : N<2^49) (hF : Legal (Ground N) F)
    (cert : HalfConstantCertificate N C) : F.card≤B N := by
  by_contra hn
  have hcard : B N≤F.card := by omega
  have hcommon := CroftKernel136.actual_original_root11 hN hhi hF hcard
  have hb := actual_original_upper_of_root11 hN hhi hNu hF cert hcommon
  omega


#print axioms actual_original_upper_of_root11
#print axioms actual_original_upper_of_certificate
end
end JSP233.HalfRecovery136
