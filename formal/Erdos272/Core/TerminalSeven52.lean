import Erdos272.Core.CoreSeven52

/-! Full physical uniform-seven exterior witnesses and terminal restoration. -/
namespace JSP233.TerminalSeven52
open StarCompletion PrivatePairExistence StarResources30 StepHall33 LongTerminal35
open ExteriorWitness36 APGeometry KKRetention32 Restore33 DenseDeletion40 JointFringe44 ThinFringe33
open TerminalDeficit51
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000

theorem exterior_intrinsic_contradiction {N c L R : ℕ} {S : Finset ℤ}
    (hN : N<2^50) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hsub : S⊆Ground N) (hc : (c:ℤ)∈S) (hbad : ¬IsAP S)
    (hcorner : ∀ Q, IntrinsicPair (c:ℤ) S Q → ExteriorPair (c:ℤ) (L:ℤ) (R:ℤ) Q)
    (hbetween : ∀ u v : ℤ, u<v → IntrinsicPair (c:ℤ) S {u,v} →
      ∃ x∈S, u<x ∧ x<v) : False := by
  have hLRZ : (L:ℤ)≤R := by exact_mod_cast hLR
  have hmin := all_intrinsic_exterior_minimum hc hbad hLRZ hcorner
  have hclosed := all_intrinsic_exterior_closed hc hcorner
  obtain ⟨d,z,hdL,hp,htail⟩ := exterior_actual_prefix hc hbad hLRZ hcorner
  have hwide : 2*(L:ℤ)≤(R:ℤ)+c := by
    exact_mod_cast (show 2*L≤R+c by omega)
  have hzL := actual_prefix_reaches_core hc hp htail hwide hbetween
  have hgrid : ∀ x∈S, (d:ℤ)∣x-c := by
    intro x hx
    by_cases hxR : x≤(R:ℤ)
    · exact hp.prefix_dvd x hx hxR
    · exact (actual_prefix_tail_grid hp hmin hzL hx (by omega) hclosed).1
  have hne : S.Nonempty := ⟨c,hc⟩
  let v := S.max' hne
  have hvS : v∈S := Finset.max'_mem S hne
  have hmax : ∀ x∈S, x≤v := fun x hx => Finset.le_max' S x hx
  have hRv : (R:ℤ)<v := by
    obtain ⟨w,hw,hRw⟩ := htail
    have hh := hmax w hw
    omega
  have hvN : v≤N := ((mem_ground N v).mp (hsub hvS)).2
  obtain ⟨h,hzeq⟩ := nat_grid_index hp.step_pos hp.top_gt.le (hp.prefix_dvd z hp.top_mem hp.top_le)
  obtain ⟨m,hveq⟩ := nat_grid_index hp.step_pos (hmin v hvS) (hgrid v hvS)
  have hdNatL : d≤L := by exact_mod_cast (show (d:ℤ)≤L by omega)
  have hmR : R<c+m*d := by
    exact_mod_cast (show (R:ℤ)<(c:ℤ)+(m:ℤ)*d by omega)
  have hmN : c+m*d≤N := by
    exact_mod_cast (show (c:ℤ)+(m:ℤ)*d≤N by omega)
  have hhalf : R+c<2*(c+h*d) := by
    have hh := (actual_prefix_tail_grid hp hmin hzL hvS hRv hclosed).2
    exact_mod_cast (show (R:ℤ)+c<2*((c:ℤ)+(h:ℤ)*d) by omega)
  obtain ⟨j,hjL,hjh,hcop⟩ := TerminalDeficit51.actual_coprime_prefix_core_seven
    hN hcL hLR hRN hp.step_pos hdNatL hthin hmR hmN hhalf
  let u : ℤ := c+(j:ℤ)*d
  have huL : (L:ℤ)≤u := by dsimp [u]; exact_mod_cast hjL
  have hcu : (c:ℤ)≤u := by dsimp [u]; exact le_add_of_nonneg_right (by positivity)
  have huz : u≤z := by
    have hm := Nat.mul_le_mul_right d hjh
    have hmZ : (j:ℤ)*d≤(h:ℤ)*d := by exact_mod_cast hm
    dsimp [u]
    omega
  have huS : u∈S := hp.fill u hcu huz ⟨(j:ℤ),by dsimp [u]; ring⟩
  have huv : u≤v := hmax u huS
  have hgcd : Int.gcd (u-c) (v-c)=d := by
    rw [hveq]
    exact coprime_grid_gcd (c:ℤ) d j m hcop
  have hcl : ∀ x, CompletionAt (c:ℤ) u v x → x∈S :=
    hclosed u huS v hvS (pair_not_exterior_lower huL (by omega))
  exact hbad (completed_maximum_grid_isAP hc hp.step_pos hcu huv hmin hmax hgrid hgcd hcl)

theorem exists_intrinsic_outside_exterior {N c L R : ℕ} {S : Finset ℤ}
    {W : Finset (Finset ℤ)} (hN : N<2^50) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hsub : S⊆Ground N) (hc : (c:ℤ)∈S) (hbad : ¬IsAP S)
    (hW : ∀ Q∈W, ExteriorPair (c:ℤ) (L:ℤ) (R:ℤ) Q)
    (hbetween : ∀ u v : ℤ, u<v → ({u,v}:Finset ℤ)∈W → ∃ x∈S, u<x ∧ x<v) :
    ∃ Q, IntrinsicPair (c:ℤ) S Q ∧ Q∉W := by
  by_contra hnone
  have hin : ∀ Q, IntrinsicPair (c:ℤ) S Q → Q∈W := by
    intro Q hQ
    by_contra hh
    exact hnone ⟨Q,hQ,hh⟩
  exact exterior_intrinsic_contradiction hN hcL hLR hRN hthin hsub hc hbad
    (fun Q hQ => hW Q (hin Q hQ))
    (fun u v huv hQ => hbetween u v huv (hin {u,v} hQ))

theorem actual_reserved_avoiding_intrinsic (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hN : N<2^50) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hv : ValidIntervals N c L R I) (hlegal : Legal (Ground N) (H∪Intervals I))
    (hroot : Rooted H (c:ℤ)) {S : Finset ℤ} (hS : S∈H) (hbad : ¬IsAP S) :
    ∃ Q, IntrinsicPair (c:ℤ) S Q ∧ Q∉Reserved c N I := by
  exact exists_intrinsic_outside_exterior hN hcL hLR hRN hthin
    (hlegal.1 S (Finset.mem_union_left _ hS)) (hroot S hS) hbad
    (fun Q hQ => (reserved_geometry N c L R I hc hLR hv hQ).2)
    (fun u v huv hQ => legal_root_interval_between N c L R H I hLR hv hlegal hroot hS huv hQ)

theorem actual_crooked_reserved_avoiding_witnesses (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hN : N<2^50) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hv : ValidIntervals N c L R I) (hlegal : Legal (Ground N) (H∪Intervals I))
    (hroot : Rooted H (c:ℤ)) : CrookedWitnesses (c:ℤ) H (Reserved c N I) := by
  intro S hS hbad
  exact actual_reserved_avoiding_intrinsic N c L R H I hN hc hcL hLR hRN hthin hv hlegal hroot hS hbad

theorem actual_root_large_with_reservation (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hN : N<2^50) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hv : ValidIntervals N c L R I) (hlegal : Legal (Ground N) (H∪Intervals I))
    (hroot : Rooted H (c:ℤ)) :
    H.card+(Reserved c N I).card≤(APSmall H).card+(c-1)/2+
      (PairUniverse (c:ℤ) (Ground N)).card := by
  have hH : Legal (Ground N) H :=
    ⟨fun S hS => hlegal.1 S (Finset.mem_union_left _ hS),
      fun S hS T hT he => hlegal.2 S (Finset.mem_union_left _ hS) T (Finset.mem_union_left _ hT) he⟩
  have hAP := CoreSeven52.actual_core_root_AP_card N c L R (APLarge H) hN hc hcL hLR hRN
    (by omega : 28*(L+N-R)≤N)
    (fun S hS => hH.1 S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2.1)
    (fun S hS => hroot S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2.2)
  have hC := crooked_outside_available_card hH hroot
    (actual_crooked_reserved_avoiding_witnesses N c L R H I hN hc hcL hLR hRN hthin hv hlegal hroot)
  have hp := actual_root_resources_with_reservation N c L R H I hc hLR hv hlegal hroot
  have hf := family_partition H
  change (APTriples H).card+(CoreAP36.CoreAPPairs N c L R (APLarge H)).card+
    (OutsideAvailable (c:ℤ) (Ground N) H (Reserved c N I)).card+(Reserved c N I).card≤
      (PairUniverse (c:ℤ) (Ground N)).card at hp
  omega

theorem actual_interval_terminal (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hN : N<2^50) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hv : ValidIntervals N c L R I) (hne : I.Nonempty)
    (hlegal : Legal (Ground N) (H∪Intervals I)) (hroot : Rooted H (c:ℤ)) :
    (H∪Intervals I).card≤N.choose 2+1 := by
  have hr := actual_root_large_with_reservation N c L R H I hN hc hcL hLR hRN hthin hv hlegal hroot
  have hs := actual_small_boundary_payment N c L R H I hc hLR hv hne hlegal hroot
  have hp := reserved_card_partition N c L R I hLR hv
  have hd : Disjoint H (Intervals I) := by
    apply Finset.disjoint_left.mpr
    intro S hS hI
    obtain ⟨p,hpI,rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨hcp,_,_,_⟩ := hv p hpI
    have hh := hroot (Interval p) hS
    simp only [Interval,Finset.mem_Icc] at hh
    omega
  have hf : (H∪Intervals I).card=H.card+I.card := by
    rw [Finset.card_union_of_disjoint hd,intervals_card N c L R I hLR hv]
  have hcN : c≤N := by omega
  have hU : (PairUniverse (c:ℤ) (Ground N)).card=(N-1).choose 2 := by
    unfold PairUniverse
    rw [Finset.card_powersetCard,Finset.card_erase_of_mem ((mem_ground _ _).mpr ⟨by omega,by omega⟩),ground_card]
  have hchoose : N.choose 2=(N-1)+(N-1).choose 2 := by
    calc
      N.choose 2=((N-1)+1).choose (1+1) := by congr 1; omega
      _=(N-1).choose 1+(N-1).choose 2 := Nat.choose_succ_succ _ _
      _=(N-1)+(N-1).choose 2 := by simp
  rw [hU] at hr
  rw [hf,hchoose]
  have hdiv : (c-1)/2≤c-1 := Nat.div_le_self _ _
  omega

theorem actual_native_interval_terminal (N c L R : ℕ) (G : Finset (Finset ℤ))
    (hN : N<2^50) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N) (hlegal : Legal (Ground N) G)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : G.card≤N.choose 2+1 := by
  obtain ⟨I,hv,hIA,hG⟩ := actual_avoider_interval_encoding N c L R G hi
  have hI : I.Nonempty := by
    obtain ⟨S,hS⟩ := hne
    rw [←hIA] at hS
    obtain ⟨p,hp,_⟩ := Finset.mem_image.mp hS
    exact ⟨p,hp⟩
  have hroot : Rooted (RootPart G (c:ℤ)) (c:ℤ) := fun S hS => (Finset.mem_filter.mp hS).2
  have hlegal' : Legal (Ground N) (RootPart G (c:ℤ)∪Intervals I) := hG ▸ hlegal
  rw [hG]
  exact actual_interval_terminal N c L R (RootPart G (c:ℤ)) I hN hc hcL hLR hRN hthin hv hI hlegal' hroot

theorem actual_native_terminal_deficit (N c L R : ℕ)
    (F G : Finset (Finset ℤ)) (P : Finset ℤ)
    (hN : N<2^50) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hlegal : Legal (Ground N) F) (hGF : G⊆F) (hPF : P∈F) (hcP : (c:ℤ)∉P)
    (hi : ∀ S∈Avoiders G (c:ℤ),∃ a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) :
    G.card+N≤N.choose 2+P.card+(L+N-R) := by
  obtain ⟨I,hv,_hIA,hG⟩ := actual_avoider_interval_encoding N c L R G hi
  let H := RootPart G (c:ℤ)
  have hroot : Rooted H (c:ℤ) := fun S hS=>(Finset.mem_filter.mp hS).2
  have hHF : H⊆F := (Finset.filter_subset _ _).trans hGF
  have hlegalG : Legal (Ground N) G :=
    ⟨fun S hS=>hlegal.1 S (hGF hS),fun S hS T hT he=>hlegal.2 S (hGF hS) T (hGF hT) he⟩
  have hlegal' : Legal (Ground N) (H∪Intervals I) := hG ▸ hlegalG
  have hr := actual_root_large_with_reservation N c L R H I hN hc hcL hLR hRN hthin hv hlegal' hroot
  have hs := actual_APSmall_external_avoider N (c:ℤ) F H P hlegal hHF hroot hPF hcP
  have hb := actual_boundary_fringe_count N c L R I hcL hLR hRN hv
  have hp := reserved_card_partition N c L R I hLR hv
  have hd : Disjoint H (Intervals I) := by
    apply Finset.disjoint_left.mpr
    intro S hS hI
    obtain ⟨p,hpI,rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨hcp,_,_,_⟩ := hv p hpI
    have hh := hroot (Interval p) hS
    simp only [Interval,Finset.mem_Icc] at hh
    omega
  have hf : G.card=H.card+I.card := by
    calc
      G.card=(H∪Intervals I).card := congrArg Finset.card hG
      _=H.card+I.card := by rw [Finset.card_union_of_disjoint hd,intervals_card N c L R I hLR hv]
  have hU : (PairUniverse (c:ℤ) (Ground N)).card=(N-1).choose 2 := by
    unfold PairUniverse
    rw [Finset.card_powersetCard,Finset.card_erase_of_mem ((mem_ground _ _).mpr ⟨by omega,by omega⟩),ground_card]
  have hchoose : N.choose 2=(N-1)+(N-1).choose 2 := by
    calc
      N.choose 2=((N-1)+1).choose (1+1) := by congr 1;omega
      _=(N-1).choose 1+(N-1).choose 2 := Nat.choose_succ_succ _ _
      _=(N-1)+(N-1).choose 2 := by simp
  rw [hU] at hr
  have hdiv : (c-1)/2≤c-1 := Nat.div_le_self _ _
  omega


theorem actual_adaptive_restore_reciprocal
    (r p r0 p0 N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : N<2^50) (hr : 0<r) (hp : r<p) (hp3 : 3≤p) (hsize : p^3≤N)
    (hr0 : 1<r0) (hp0 : r0<p0) (hp03 : 3≤p0) (hsize0 : p0^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hgeometry : r*p*(L+N-R)≤(p-r)*N)
    (hsmallpay : r0*(JointCount p+1)*(L+N-R)≤(r0-1)*N)
    (hgeometry0 : r0*p0*(L+N-R)≤(p0-r0)*N)
    (hquarter0 : 4*JointCount p0*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<r*S.card)
    (havoid : ∀S∈E,(c:ℤ)∉S)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  have hGF : G⊆F := by rw [hG];exact Finset.sdiff_subset
  have hGlegal := RestoreTerminal35.retained_legal hG hlegal
  have ht := actual_native_interval_terminal N c L R G hN hc hcL hLR hRN hthin hGlegal hne hi
  have hcard := deletion_card_exact F E hEF
  rw [←hG] at hcard
  by_cases he : E.Nonempty
  · obtain ⟨P,hPE,hmin⟩ := Finset.exists_min_image E Finset.card he
    by_cases hm : r0*P.card≤N
    · have hd := actual_native_terminal_deficit N c L R F G P hN hc hcL hLR hRN hthin
        hlegal hGF (hEF hPE) (havoid P hPE) hi
      have hb := TerminalDeficit51.actual_interval_fringe_count r p N c L R F G E hr hp hp3 hsize
        hc hcL hLR hRN hgeometry hGF hEF hlegal hbad hdense hne hi
      have hf : E.card≤JointCount p*(L+N-R) := hb.trans
        (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      have hd' := Nat.mul_le_mul_left r0 hd
      have hf' := Nat.mul_le_mul_left r0 hf
      have hcard' := congrArg (fun n=>r0*n) hcard
      have hco : (r0-1)*N+N=r0*N := by
        calc
          (r0-1)*N+N=((r0-1)+1)*N := by ring
          _=r0*N := by congr 1;omega
      have hbound : r0*F.card≤r0*N.choose 2 := by
        nlinarith only [hd',hf',hcard',hm,hsmallpay,hco]
      have hfinal : F.card≤N.choose 2 := by
        by_contra hn
        have hh := Nat.mul_le_mul_left r0 (show N.choose 2+1≤F.card by omega)
        nlinarith only [hh,hbound,hr0]
      unfold B
      omega
    · have hd0 : ∀S∈E,N<r0*S.card := by
        intro S hS
        have hs := Nat.mul_le_mul_left r0 (hmin S hS)
        omega
      have hb := TerminalDeficit51.actual_interval_fringe_count r0 p0 N c L R F G E (by omega) hp0 hp03 hsize0
        hc hcL hLR hRN hgeometry0 hGF hEF hlegal hbad hd0 hne hi
      have hpay := quarter_payment (JointCount p0) N (L+N-R) (by omega) hquarter0
      unfold B
      omega
  · have hE : E=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hE,Finset.card_empty,add_zero] at hcard
    unfold B
    omega

theorem actual_deleted_avoider_restore_reciprocal
    (r p r0 p0 N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : N<2^50) (hr : 0<r) (hp : r<p) (hp3 : 3≤p) (hsize : p^3≤N)
    (hr0 : 1<r0) (hp0 : r0<p0) (hp03 : 3≤p0) (hsize0 : p0^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hgeometry : r*p*(L+N-R)≤(p-r)*N)
    (hsmallpay : r0*(JointCount p+1)*(L+N-R)≤(r0-1)*N)
    (hgeometry0 : r0*p0*(L+N-R)≤(p0-r0)*N)
    (hquarter0 : 4*JointCount p0*(L+N-R)≤N)
    (hlegal : Legal (Ground N) F) (hne : (Avoiders (Retained N r F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N r F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  let E := OmittedAvoiders N r F (c:ℤ)
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N r F)
  have ha := actual_avoider_readdition N r F (c:ℤ)
  apply actual_adaptive_restore_reciprocal r p r0 p0 N c L R F (F\E) E
    hN hr hp hp3 hsize hr0 hp0 hp03 hsize0 hc hcL hLR hRN hthin
    hgeometry hsmallpay hgeometry0 hquarter0 rfl hEF hlegal
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · simpa only [E,ha] using hne
  · simpa only [E,ha] using hi

theorem actual_adaptive_restore (r p N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : N<2^50) (hr : 0<r) (hp : r<p) (hp3 : 3≤p) (hsize : p^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hgeometry : r*p*(L+N-R)≤(p-r)*N)
    (hhalf : 2*(JointCount p+1)*(L+N-R)≤N) (hquarter : 28*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<r*S.card)
    (havoid : ∀S∈E,(c:ℤ)∉S)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  have hj : JointCount 3=7 := by norm_num [JointCount,ShortCount,Finset.sum_Icc_succ_top]
  exact actual_adaptive_restore_reciprocal r p 2 3 N c L R F G E hN hr hp hp3 hsize
    (by decide) (by decide) (by decide) ((Nat.pow_le_pow_left hp3 3).trans hsize)
    hc hcL hLR hRN hthin hgeometry (by simpa using hhalf) (by omega)
    (by simpa only [hj] using hquarter) hG hEF hlegal hbad hdense havoid hne hi

theorem actual_deleted_avoider_restore (r p N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : N<2^50) (hr : 0<r) (hp : r<p) (hp3 : 3≤p) (hsize : p^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hgeometry : r*p*(L+N-R)≤(p-r)*N)
    (hhalf : 2*(JointCount p+1)*(L+N-R)≤N) (hquarter : 28*(L+N-R)≤N)
    (hlegal : Legal (Ground N) F) (hne : (Avoiders (Retained N r F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N r F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  have hj : JointCount 3=7 := by norm_num [JointCount,ShortCount,Finset.sum_Icc_succ_top]
  exact actual_deleted_avoider_restore_reciprocal r p 2 3 N c L R F hN hr hp hp3 hsize
    (by decide) (by decide) (by decide) ((Nat.pow_le_pow_left hp3 3).trans hsize)
    hc hcL hLR hRN hthin hgeometry (by simpa using hhalf) (by omega)
    (by simpa only [hj] using hquarter) hlegal hne hi

#print axioms exterior_intrinsic_contradiction
#print axioms exists_intrinsic_outside_exterior
#print axioms actual_reserved_avoiding_intrinsic
#print axioms actual_crooked_reserved_avoiding_witnesses
#print axioms actual_root_large_with_reservation
#print axioms actual_interval_terminal
#print axioms actual_native_interval_terminal
#print axioms actual_native_terminal_deficit
#print axioms actual_adaptive_restore_reciprocal
#print axioms actual_deleted_avoider_restore_reciprocal
#print axioms actual_adaptive_restore
#print axioms actual_deleted_avoider_restore
end
end JSP233.TerminalSeven52
