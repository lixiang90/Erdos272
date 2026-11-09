module

public import Erdos272.Traces.FlexibleTrace44
public import Erdos272.Counting.OffResidue44

@[expose] public section

/-! Actual off-residue packing and aligned private-point code compression,
assembled into the original-family long-interval restoration theorem. -/
namespace JSP233.JointFringe44
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33 DenseDeletion40
open scoped Classical BigOperators
noncomputable section

abbrev Key := Σ _d : ℕ,ℕ×ℕ
abbrev Origin (p N : ℕ) (k : Key) : ℤ := ThinFringe42.AnchorPoint (p-1) N k

def ShortKeys (p : ℕ) : Finset (Σ _d : ℕ,ℕ) :=
  (Finset.Icc 1 (p-1)).sigma (fun d=>Finset.Icc 1 (p/d))

def ShortCount (p : ℕ) : ℕ := ∑ d∈Finset.Icc 1 (p-1),p/d
def JointCount (p : ℕ) : ℕ := p+ShortCount p

def Aligned (K : Finset ℤ→Key) (p N : ℕ) (S : Finset ℤ) : Prop :=
  ∀ y∈S,((K S).1:ℤ)∣y-Origin p N (K S)

theorem short_keys_card (p : ℕ) : (ShortKeys p).card=ShortCount p := by
  simp [ShortKeys,ShortCount,Finset.card_sigma]

theorem joint_count28 : JointCount 28=128 := by
  norm_num [JointCount,ShortCount,Finset.sum_Icc_succ_top]

theorem joint_count41 : JointCount 41=200 := by
  norm_num [JointCount,ShortCount,Finset.sum_Icc_succ_top]

theorem residue_dvd {p N : ℕ} {k : Key} {y : ℤ}
    (h : (k.1:ℤ)∣y-Origin p N k) : (k.1:ℤ)∣y-(k.2.1:ℤ) := by
  have hg : (k.1:ℤ)∣Origin p N k-(k.2.1:ℤ) := by
    refine ⟨(k.2.2:ℤ)*(N/(p-1+1):ℕ),?_⟩
    dsimp [Origin,ThinFringe42.AnchorPoint]
    ring
  have hh := Int.dvd_add h hg
  convert hh using 1
  ring

theorem bounded_residue_eq {d a b : ℕ} {y : ℤ} (hd : 0<d)
    (ha : 1≤a ∧ a≤d) (hb : 1≤b ∧ b≤d)
    (hya : (d:ℤ)∣y-(a:ℤ)) (hyb : (d:ℤ)∣y-(b:ℤ)) : a=b := by
  have hab : (d:ℤ)∣(a:ℤ)-(b:ℤ) := by
    have hh := Int.dvd_sub hyb hya
    convert hh using 1
    ring
  obtain ⟨z,hz⟩ := hab
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  have hlo : -(d:ℤ)<(a:ℤ)-(b:ℤ) := by omega
  have hhi : (a:ℤ)-(b:ℤ)<(d:ℤ) := by omega
  have hzlo : 0≤z := by
    by_contra hn
    have hh := mul_nonneg hdZ.le (by omega : (0:ℤ)≤-z-1)
    nlinarith only [hz,hlo,hh]
  have hzhi : z≤0 := by
    by_contra hn
    have hh := mul_nonneg hdZ.le (by omega : (0:ℤ)≤z-1)
    nlinarith only [hz,hhi,hh]
  have he : z=0 := by omega
  rw [he,mul_zero] at hz
  omega

theorem actual_aligned_private {N p : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (K : Finset ℤ→Key) (hlegal : Legal (Ground N) E) (hbad : ∀ S∈E,¬IsAP S)
    (hanchor : ∀ S∈E,ThinFringe42.HasAnchor (p-1) N L R (K S) S) :
    ∀ S∈E.filter (Aligned K p N),∃ y,y∈S ∧ y∉Finset.Icc L R ∧
      ∀ T∈E.filter (Aligned K p N),K T=K S → T≠S → y∉T := by
  let A := E.filter (Aligned K p N)
  intro S hS
  let C := A.filter (fun T=>K T=K S)
  have hCS : S∈C := Finset.mem_filter.mpr ⟨hS,rfl⟩
  have hCE : C⊆E := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hc : ∀ T∈C,ThinFringe42.HasAnchor (p-1) N L R (K S) T := by
    intro T hT
    have he := (Finset.mem_filter.mp hT).2
    simpa only [he] using hanchor T (hCE hT)
  obtain ⟨y,hy,hyI,hprivate⟩ := ThinFringe33.actual_class_private_point
    (fun T hT=>hbad T (hCE hT))
    (fun T hT U hU hne=>hlegal.2 T (hCE hT) U (hCE hU) hne)
    (fun T hT=>(hc T hT).1) (fun T hT=>(hc T hT).2.1)
    (fun T hT=>(hc T hT).2.2) hCS
  refine ⟨y,hy,hyI,?_⟩
  intro T hT he hne
  exact hprivate T (Finset.mem_filter.mpr ⟨hT,he⟩) hne

theorem actual_aligned_count {N p : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (hp : 3≤p) (K : Finset ℤ→Key) (hlegal : Legal (Ground N) E)
    (hbad : ∀ S∈E,¬IsAP S)
    (hkeys : ∀ S∈E,K S∈ThinFringe42.AnchorKeys (p-1))
    (hanchor : ∀ S∈E,ThinFringe42.HasAnchor (p-1) N L R (K S) S) :
    (E.filter (Aligned K p N)).card≤ShortCount p*(Ground N\Finset.Icc L R).card := by
  let A := E.filter (Aligned K p N)
  have hex := actual_aligned_private K hlegal hbad hanchor
  choose Y hY using hex
  have hp1 : p-1+1=p := by omega
  have hshort : ∀ S∈A,(⟨(K S).1,(K S).2.2⟩:Σ _d:ℕ,ℕ)∈ShortKeys p := by
    intro S hS
    obtain ⟨hd,hrj⟩ := Finset.mem_sigma.mp (hkeys S (Finset.mem_filter.mp hS).1)
    have hj := (Finset.mem_product.mp hrj).2
    apply Finset.mem_sigma.mpr
    exact ⟨hd,by simpa only [hp1] using hj⟩
  have hc : A.card≤((ShortKeys p).product (Ground N\Finset.Icc L R)).card := by
    apply Finset.card_le_card_of_injective (f:=fun S:A=>
      (⟨(⟨(K S.val).1,(K S.val).2.2⟩,Y S.val S.property),Finset.mem_product.mpr
        ⟨hshort S.val S.property,Finset.mem_sdiff.mpr
          ⟨hlegal.1 S.val (Finset.mem_filter.mp S.property).1 (hY S.val S.property).1,
            (hY S.val S.property).2.1⟩⟩⟩ : ↥((ShortKeys p).product (Ground N\Finset.Icc L R))))
    intro S T he
    apply Subtype.ext
    by_contra hne
    have hcode := congrArg Subtype.val he
    have hd : (K S.val).1=(K T.val).1 := congrArg (fun z:(Σ _d:ℕ,ℕ)×ℤ=>z.1.1) hcode
    have hj : (K S.val).2.2=(K T.val).2.2 := congrArg (fun z:(Σ _d:ℕ,ℕ)×ℤ=>z.1.2) hcode
    have hy : Y S.val S.property=Y T.val T.property := congrArg Prod.snd hcode
    obtain ⟨hds,hrjs⟩ := Finset.mem_sigma.mp (hkeys S.val (Finset.mem_filter.mp S.property).1)
    obtain ⟨hdt,hrjt⟩ := Finset.mem_sigma.mp (hkeys T.val (Finset.mem_filter.mp T.property).1)
    have hrs := Finset.mem_Icc.mp (Finset.mem_product.mp hrjs).1
    have hrt := Finset.mem_Icc.mp (Finset.mem_product.mp hrjt).1
    have hAS : Aligned K p N S.val := (Finset.mem_filter.mp S.property).2
    have hAT : Aligned K p N T.val := (Finset.mem_filter.mp T.property).2
    have hresS := residue_dvd (hAS _ (hY S.val S.property).1)
    have hresT := residue_dvd (hAT _ (hY T.val T.property).1)
    rw [←hy,←hd] at hresT
    have hrt' : 1≤(K T.val).2.1 ∧ (K T.val).2.1≤(K S.val).1 := by omega
    have hrho := bounded_residue_eq (by have hh := (Finset.mem_Icc.mp hds).1;omega) hrs hrt' hresS hresT
    have hkEq : K S.val=K T.val := Sigma.ext hd (heq_of_eq (Prod.ext hrho hj))
    have hyT : Y S.val S.property∈T.val := by rw [hy];exact (hY T.val T.property).1
    exact (hY S.val S.property).2.2 T.val T.property hkEq.symm (Ne.symm hne) hyT
  have he := Finset.card_product (ShortKeys p) (Ground N\Finset.Icc L R)
  exact hc.trans_eq (he.trans (by rw [short_keys_card]))

theorem actual_joint_from_anchors {N p : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (hp : 3≤p) (hN : p^3≤N) (K : Finset ℤ→Key) (hlegal : Legal (Ground N) E)
    (hbad : ∀ S∈E,¬IsAP S)
    (hkeys : ∀ S∈E,K S∈ThinFringe42.AnchorKeys (p-1))
    (hanchor : ∀ S∈E,ThinFringe42.HasAnchor (p-1) N L R (K S) S)
    (hlong : ∀ S∈E,N<p*(S∩Finset.Icc L R).card) :
    E.card≤JointCount p*(Ground N\Finset.Icc L R).card := by
  let d : Finset ℤ→ℤ := fun S=>(K S).1
  let a := fun S : Finset ℤ=>Origin p N (K S)
  have ho := OffResidue44.actual_off_residue_count (Ground N) E L R d a p (by omega)
    (by simpa only [ground_card] using hN) hlegal (fun S hS=>(hanchor S hS).1)
    (by intro S hS;simpa only [ground_card] using hlong S hS)
  have ha := actual_aligned_count hp K hlegal hbad hkeys hanchor
  have he : E.filter (fun S=>¬Aligned K p N S)=OffResidue44.OffMembers E d a := by
    ext S
    simp [Aligned,OffResidue44.OffMembers,d,a]
  have hc := Finset.card_filter_add_card_filter_not (s:=E) (Aligned K p N)
  rw [he] at hc
  dsimp [JointCount]
  nlinarith only [ho,ha,hc]

theorem actual_dense_fringe_bound (r p N : ℕ) (hr : 0<r) (hp : r<p) (hp3 : 3≤p)
    (hN : p^3≤N) (F E : Finset (Finset ℤ)) (L R : ℤ)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀ S∈E,¬IsAP S)
    (hdense : ∀ S∈E,N<r*S.card) (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ))
    (hcore : ∃ H∈F,IsAP H ∧ Finset.Icc L R⊆H)
    (hthin : r*p*((Ground N\Finset.Icc L R).card+1)≤(p-r)*N) :
    E.card≤JointCount p*(Ground N\Finset.Icc L R).card := by
  have hN2 : p^2≤N := by
    have hh : p^2≤p^3 := by have := Nat.mul_le_mul_left (p^2) (show 1≤p by omega);nlinarith only [this]
    exact hh.trans hN
  have hcover := FlexibleTrace44.actual_dense_anchor_cover r p N hr hp hp3 hN2 F E L R
    hlegal hEF hbad hdense hL hLR hR hcore hthin
  let K : Finset ℤ→Key := fun S=>if h:S∈E then Classical.choose (hcover S h) else ⟨1,1,1⟩
  have hK : ∀ S∈E,K S∈ThinFringe42.AnchorKeys (p-1) ∧
      ThinFringe42.HasAnchor (p-1) N L R (K S) S := by
    intro S hS
    simpa only [K,dif_pos hS] using Classical.choose_spec (hcover S hS)
  have hElegal : Legal (Ground N) E :=
    ⟨fun S hS=>hlegal.1 S (hEF hS),fun S hS T hT hne=>hlegal.2 S (hEF hS) T (hEF hT) hne⟩
  apply actual_joint_from_anchors hp3 hN K hElegal hbad (fun S hS=>(hK S hS).1) (fun S hS=>(hK S hS).2)
  intro S hS
  have hc := card_le_trace_add_exterior (K:=Finset.Icc L R) (hlegal.1 S (hEF hS))
  have hm := FlexibleTrace44.trace_count_lower r p N (S∩Finset.Icc L R).card
    (Ground N\Finset.Icc L R).card hr hp ((hdense S hS).trans_le (Nat.mul_le_mul_left r hc)) hthin
  exact (Nat.lt_mul_div_succ N (by omega : 0<p)).trans_le (Nat.mul_le_mul_left p (by omega))

theorem quarter_payment (b N t : ℕ) (hN : 1≤N) (hpay : 4*b*t≤N) : b*(t-1)≤(N-1)/4 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  by_cases hb : b=0
  · simp [hb]
  by_cases ht : t=0
  · simp [ht]
  have he : t-1+1=t := by omega
  have hm : b*(t-1)+b=b*t := by nlinarith only [he]
  have hb1 : 1≤b := by omega
  have hN1 : N-1+1=N := by omega
  nlinarith

theorem actual_long_core_restore (r p N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hr : 0<r) (hp : r<p) (hp3 : 3≤p) (hN : p^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hgeometry : r*p*(L+N-R)≤(p-r)*N) (hquarter : 4*JointCount p*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈E,¬IsAP S) (hdense : ∀ S∈E,N<r*S.card)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ),∃ a b:ℕ,c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) :
    F.card≤B N := by
  have ht := Terminal36.actual_native_interval_terminal N c L R G hc hcL hLR hRN hthin
    (RestoreTerminal35.retained_legal hG hlegal) hne hi
  obtain ⟨H,hHG,hHAP,hKH⟩ := RestoreTerminal35.actual_interval_core_member N c L R G hLR hne hi
  have hHF : H∈F := by rw [hG] at hHG;exact (Finset.mem_sdiff.mp hHG).1
  have ho := ground_interval_exterior_card N (by omega : (1:ℤ)≤L)
    (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
  have he : (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card+1=L+N-R := by omega
  have hb := actual_dense_fringe_bound r p N hr hp hp3 hN F E (L:ℤ) (R:ℤ)
    hlegal hEF hbad hdense (by omega) (by exact_mod_cast hLR) (by exact_mod_cast hRN)
    ⟨H,hHF,hHAP,hKH⟩ (by rw [he];exact hgeometry)
  have he' : (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card=(L+N-R)-1 := by omega
  rw [he'] at hb
  have hE := hb.trans (quarter_payment (JointCount p) N (L+N-R) (by omega) hquarter)
  have hcard := deletion_card_exact F E hEF
  rw [←hG] at hcard
  unfold B
  omega

theorem actual_deleted_long_core_restore39_41 (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : 41^3≤N) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N) (hquarter : 800*(L+N-R)≤N)
    (hlegal : Legal (Ground N) F)
    (hne : (Avoiders (Retained N 39 F) (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders (Retained N 39 F) (c:ℤ),∃ a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) : F.card≤B N := by
  apply actual_long_core_restore 39 41 N c L R F (Retained N 39 F) (Deleted N 39 F)
    (by decide) (by decide) (by decide) hN hc hcL hLR hRN hthin
    (FlexibleTrace44.geometry39_41_of_quarter800 N (L+N-R) hquarter) ?_ rfl
    (actual_deleted_subset N 39 F) hlegal
    (fun S hS=>(Finset.mem_filter.mp hS).2.1) (fun S hS=>(Finset.mem_filter.mp hS).2.2) hne hi
  simpa only [joint_count41,show 4*200=800 by norm_num] using hquarter

#print axioms short_keys_card
#print axioms joint_count28
#print axioms joint_count41
#print axioms residue_dvd
#print axioms bounded_residue_eq
#print axioms actual_aligned_private
#print axioms actual_aligned_count
#print axioms actual_joint_from_anchors
#print axioms actual_dense_fringe_bound
#print axioms quarter_payment
#print axioms actual_long_core_restore
#print axioms actual_deleted_long_core_restore39_41
end
end JSP233.JointFringe44
