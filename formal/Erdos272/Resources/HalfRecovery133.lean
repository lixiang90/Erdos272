module

public import Erdos272.Resources.HalfPrepared133
public import Erdos272.Resources.PairRecovery131

@[expose] public section

namespace JSP233.HalfRecovery133
open StarCompletion APGeometry CoprimeDensity52 MiddleJoint51 MiddleDeficit52
open PreparedClasses50 APPrepare49 PreparedWitness48 MiddleCoordinates51
open DenseDeletion40 DenseSharper41 FamilyReflect43 RestrictedWitness44 LongTerminal35
open LinearOmitters43 OutsideEnvelope43 OneSided47 Straddling47 APCount41
open HarmonicAbel29 HarmonicLog55 RawEndpoint112 RawEndpoint115
open scoped Classical BigOperators
open HalfBad133 HalfPrepared133 PairRecovery131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def HalfConstantCertificate (N : ℕ) (C : ℝ) : Prop :=
  (∀c∈Ground N,(HalfWitnessException (Ground N) c:ℝ)+(N:ℝ)*Extra N≤(N:ℝ)*C) ∧
  (32:ℝ)^2*Rho*(C+9677/20)≤(N:ℝ) ∧
  (900/23:ℝ)^2*Rho*C≤(N:ℝ)

theorem actual_prepared_family_raw_profile {N c L R : ℕ} {G : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN100 : 100000≤N) (_hc : (c:ℤ)∈Ground N) (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈G) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈G) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    (G.card:ℝ)≤(N:ℝ)^2/2-ProfileDeficit L (N-R)+
      (HalfWitnessException (Ground N) (c:ℤ):ℝ)+2*N*(Real.log N)^2+
      (61/25)*N*Real.log N+(89/10)*N*Harmonic N+24*N+(86/25)*N+(L-c:ℕ)+3+987/200 := by
  obtain ⟨x,p,hx⟩ := actual_prepared_witness_choices hG hroot
    (by exact_mod_cast hcL.le : (c:ℤ)≤L) (by exact_mod_cast hLR : (L:ℤ)≤R) hT hcT hTR
  have hp := actual_joint_preparation_loss_half hG hroot hP hcP hLP
  have hm := EndpointExterior55.actual_prepared_middle_reduction x p hG hcL hLR hRN hP hLP hroot
    houtside (fun S hS=>⟨(hx S hS).1,(hx S hS).2.2.1,
      (hx S hS).2.2.2.2.1,(hx S hS).2.2.2.2.2⟩)
  have hr := RawEndpoint121.actual_prepared_CM_EM_profile x p (by omega : 16≤N) hG hcL.le hLR hRN hroot hP hLP
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.1,(hx S hS).2.2.2.1⟩)
  nlinarith only [hp,hm,hr]

theorem actual_readded11_raw_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN100 : 100000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    (F.card:ℝ)≤(N:ℝ)^2/2-ProfileDeficit L (N-R)+
      (HalfWitnessException (Ground N) (c:ℤ):ℝ)+2*N*(Real.log N)^2+
      (61/25)*N*Real.log N+(89/10)*N*Harmonic N+24*N+(86/25)*N+(L-c:ℕ)+3+987/200+
      (TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)).card := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)
  let G := RawEndpoint114.Readded N F (c:ℤ)
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have hGF : G⊆F := Finset.sdiff_subset
  have hGlegal : Legal (Ground N) G := ⟨fun S hS=>hF.1 S (hGF hS),
    fun S hS U hU he=>hF.2 S (hGF hS) U (hGF hU) he⟩
  have hsub := RawEndpoint114.actual_retained_subset_readded N F (c:ℤ)
  have ha := TerminalDeficit51.actual_avoider_readdition N 11 F (c:ℤ)
  have hout : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v := by
    intro S hS hcS
    have hv : S∈Avoiders G (c:ℤ) := Finset.mem_filter.mpr ⟨hS,hcS⟩
    change Avoiders G (c:ℤ)=_ at ha
    rw [ha] at hv
    exact houtside S (Finset.mem_filter.mp hv).1 hcS
  have hr := actual_prepared_family_raw_profile hN100 hc hGlegal hcL hLR hRN
    (RawEndpoint114.actual_readded_root hroot) (hsub hP) hcP hLP (hsub hT) hcT hTR hout
  have hcard := Finset.card_sdiff_add_card_eq_card hEF
  have hcardR : (G.card:ℝ)+E.card=F.card := by exact_mod_cast hcard
  dsimp only [E] at hcardR
  linarith only [hr,hcardR]


theorem actual_readded11_bootstrap_profile_width {N c L R : ℕ} {C : ℝ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 100000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hthin : 32*(L+N-R)≤N)
    (hbudget : (HalfWitnessException (Ground N) (c:ℤ):ℝ)+(N:ℝ)*Extra N≤(N:ℝ)*C) :
    RawEndpoint115.ProfileDeficit L (N-R)≤(N:ℝ)*C := by
  have hr := actual_readded11_raw_profile hN hc hF hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside
  have hne : (Avoiders (Retained N 11 F) (c:ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨hP,hcP⟩⟩
  have hcount := RawEndpoint116.actual_deleted_avoider_count68 (by omega : 4913≤N) hc hF hcL hLR hRN hne hi hthin
  have hcount' := hcount.trans (Nat.mul_le_mul_left 68 (Nat.sub_le (L+N-R) 1))
  have hcountR : ((TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)).card:ℝ)≤
      68*((L+N-R:ℕ):ℝ) := by exact_mod_cast hcount'
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1≤N) hcard
  have hn : (3000:ℝ)≤N := by exact_mod_cast (show 3000≤N by omega)
  have he : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N-R) := by
    rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add];ring
  rw [he] at hcountR
  have ht : (32:ℝ)*((L:ℝ)+(N-R))≤N := by
    have hh : (32:ℝ)*((L+N-R:ℕ):ℝ)≤N := by exact_mod_cast hthin
    rwa [he] at hh
  have hd : ((L-c:ℕ):ℝ)≤(L:ℝ)+(N-R) := by
    have hh : ((L-c:ℕ):ℝ)≤((L+N-R:ℕ):ℝ) := by exact_mod_cast (by omega : L-c≤L+N-R)
    rwa [he] at hh
  have hcost : RawEndpoint115.ProfileDeficit L (N-R)≤
      (HalfWitnessException (Ground N) (c:ℤ):ℝ)+(N:ℝ)*Extra N := by
    dsimp only [Extra]
    nlinarith only [hr,hb,hcountR,ht,hd,hn]
  exact hcost.trans hbudget

theorem actual_readded11_bootstrap_width {N c L R : ℕ} {C : ℝ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 100000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hthin : 32*(L+N-R)≤N)
    (hbudget : (HalfWitnessException (Ground N) (c:ℤ):ℝ)+(N:ℝ)*Extra N≤(N:ℝ)*C) :
    ((L:ℝ)+(N-R))^2≤(N:ℝ)*(Rho*C) := by
  have hp := actual_readded11_bootstrap_profile_width hN hc hF hcard hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside hi hthin hbudget
  have he := RawEndpoint115.profile_square_identity (L:ℝ) ((N:ℝ)-R)
  have hs := sq_nonneg (329*((N:ℝ)-R)-(49159/200:ℝ)*L)
  dsimp only [DeficitCoeff] at he
  dsimp only [Rho]
  nlinarith only [hp,he,hs]

theorem actual_retained11_profile {N c L R : ℕ} {C : ℝ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 100000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hbudget : (HalfWitnessException (Ground N) (c:ℤ):ℝ)+(N:ℝ)*Extra N≤(N:ℝ)*C) :
    ProfileDeficit L (N-R)≤(N:ℝ)*(C+9677/20) := by
  have hr := actual_prepared_family_raw_profile hN
    hc (actual_retained_legal hF) hcL hLR hRN hroot hP hcP hLP hT hcT hTR houtside
  have hd := actual_retained_sharp_lower (r:=11) (by decide : 0<11)
    (by norm_num;omega) hF
  have hdR : (F.card:ℝ)≤(Retained N 11 F).card+485*(N:ℝ) := by exact_mod_cast hd
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1≤N) hcard
  have hn : (100000:ℝ)≤N := by exact_mod_cast hN
  have hL : ((L-c:ℕ):ℝ)≤N := by exact_mod_cast (show L-c≤N by omega)
  have hcost : ProfileDeficit L (N-R)≤
      (HalfWitnessException (Ground N) (c:ℤ):ℝ)+(N:ℝ)*
      (2*(Real.log N)^2+(61/25)*Real.log N+(89/10)*Harmonic N+5137/10) := by
    nlinarith only [hr,hdR,hb,hn,hL]
  dsimp only [Extra] at hbudget
  nlinarith only [hcost,hbudget]

theorem actual_retained11_width {N c L R : ℕ} {C : ℝ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 100000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hbudget : (HalfWitnessException (Ground N) (c:ℤ):ℝ)+(N:ℝ)*Extra N≤(N:ℝ)*C) :
    ((L:ℝ)+(N-R))^2≤(N:ℝ)*(Rho*(C+9677/20)) := by
  have hp := actual_retained11_profile hN hc hF hcard hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside hbudget
  have he := profile_square_identity (L:ℝ) ((N:ℝ)-R)
  have hs := sq_nonneg (329*((N:ℝ)-R)-(49159/200:ℝ)*L)
  dsimp only [DeficitCoeff] at he
  dsimp only [Rho]
  nlinarith only [hp,he,hs]

theorem actual_original_upper_of_root11 {N : ℕ} {C : ℝ} {F : Finset (Finset ℤ)}
    (hN : 74320000≤N) (hNu : N<2^49) (hF : Legal (Ground N) F)
    (cert : HalfConstantCertificate N C)
    (hcommon : ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S) : F.card≤B N := by
  obtain ⟨hbudget,hcoarse,hfine⟩ := cert
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
    have hwCoarse := actual_retained11_width (by omega : 100000≤N) hc' hLH hcardH
      hcL hLR hRN hroot' hPF hcP hLP hTF hcT hTR houtside (hbudget _ hc')
    have he : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N-R) := by
      rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add]
      ring
    have hwCoarseNat : ((L+N-R:ℕ):ℝ)^2≤(N:ℝ)*(Rho*(C+9677/20)) := by
      rwa [he]
    have hthin := actual_preliminary_width_payment hcoarse hwCoarseNat
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
      have hw := actual_readded11_bootstrap_width (by omega : 100000≤N)
        hc' hLH hcardH hcL hLR hRN hroot' hPF hcP hLP hTF hcT hTR houtside hi hthin (hbudget _ hc')
      have hwNat : ((L+N-R:ℕ):ℝ)^2≤(N:ℝ)*(Rho*C) := by
        rwa [he]
      have hpay := actual_balanced_width_payment hfine hwNat
      have hprofile := actual_readded11_bootstrap_profile_width
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
    (hN : 74320000≤N) (hNu : N<2^49) (hF : Legal (Ground N) F)
    (cert : HalfConstantCertificate N C) : F.card≤B N := by
  by_contra hn
  have hcard : B N≤F.card := by omega
  have hcommon := CroftKernel113.actual_original_root11 hN hNu hF hcard
  have hb := actual_original_upper_of_root11 hN hNu hF cert hcommon
  omega

#print axioms actual_prepared_family_raw_profile
#print axioms actual_readded11_raw_profile
#print axioms actual_readded11_bootstrap_profile_width
#print axioms actual_readded11_bootstrap_width
#print axioms actual_retained11_profile
#print axioms actual_retained11_width
#print axioms actual_original_upper_of_root11
#print axioms actual_original_upper_of_certificate
end
end JSP233.HalfRecovery133
