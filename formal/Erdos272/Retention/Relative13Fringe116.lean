module

public import Erdos272.Retention.Ceil13Fringe116

@[expose] public section

/-! The ceil grid is built on the actual interval I, but the original sources
remain Legal on Ground N. Off traces are packed in I; full sources are not
mistaken for subsets of that interval. -/
namespace JSP233.Relative13Fringe116
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

abbrev Key := Ceil13Fringe116.Key
abbrev Keys := Ceil13Fringe116.Keys
abbrev ShortKeys := Ceil13Fringe116.ShortKeys

def Origin (M : ℕ) (L : ℤ) (k : Key) : ℤ := L-1+Ceil13Fringe116.Origin M k

def HasAnchor (M : ℕ) (L R : ℤ) (k : Key) (S : Finset ℤ) : Prop :=
  APAt (k.1:ℤ) (Origin M L k) (S∩Finset.Icc L R) ∧
    Origin M L k∈S∩Finset.Icc L R ∧ Origin M L k+(k.1:ℤ)∈S∩Finset.Icc L R

theorem short_keys_card : ShortKeys.card=35 := Ceil13Fringe116.short_keys_card

theorem interval_card {L R : ℕ} (hLR : L≤R) :
    (Finset.Icc (L:ℤ) (R:ℤ)).card=R-L+1 := by
  simp only [Int.card_Icc]
  omega

theorem actual_trace_anchor {S H : Finset ℤ} {L R : ℕ}
    (hL : 1≤L) (hLR : L≤R) (hM : 169≤R-L+1)
    (hpair : IsAP (S∩H)) (hKH : Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hm : (R-L+1)/13+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    ∃k∈Keys,HasAnchor (R-L+1) (L:ℤ) (R:ℤ) k S := by
  let M := R-L+1
  let m := (S∩Finset.Icc (L:ℤ) (R:ℤ)).card
  obtain ⟨d,a0,hAP⟩ := apAt_interval_trace hpair hKH
  have hd := hAP.1
  have hne : (S∩Finset.Icc (L:ℤ) (R:ℤ)).Nonempty := Finset.card_pos.mp (by omega)
  let a := (S∩Finset.Icc (L:ℤ) (R:ℤ)).min' hne
  let b := (S∩Finset.Icc (L:ℤ) (R:ℤ)).max' hne
  have haS : a∈S∩Finset.Icc (L:ℤ) (R:ℤ) := Finset.min'_mem _ hne
  have hbS : b∈S∩Finset.Icc (L:ℤ) (R:ℤ) := Finset.max'_mem _ hne
  have haK := Finset.mem_Icc.mp (Finset.mem_inter.mp haS).2
  have hbK := Finset.mem_Icc.mp (Finset.mem_inter.mp hbS).2
  have haCast : (a.toNat:ℤ)=a := Int.toNat_of_nonneg (by omega)
  have hbCast : (b.toNat:ℤ)=b := Int.toNat_of_nonneg (by omega)
  have hdCast : (d.toNat:ℤ)=d := Int.toNat_of_nonneg hd.le
  have hspan := apAt_span_eq hAP hne
  have hMc : (M:ℤ)=(R:ℤ)-L+1 := by dsimp only [M];omega
  have hbound : d*((m:ℤ)-1)≤(M:ℤ)-1 := by dsimp only [m];omega
  have hNq : M<13*(M/13+1) := Nat.lt_mul_div_succ M (by decide)
  have hNqZ : (M:ℤ)<13*((M/13:ℕ)+1:ℕ) := by exact_mod_cast hNq
  have hmm : (M/13:ℕ)+1≤m-1 := by dsimp only [M,m];omega
  have hmmZ : ((M/13:ℕ)+1:ℕ)≤((m:ℤ)-1) := by omega
  have hdr : d≤12 := by
    by_contra hn
    have hdp : (13:ℤ)≤d := by omega
    have hmul := mul_le_mul_of_nonneg_right hdp (show (0:ℤ)≤(m:ℤ)-1 by omega)
    have hmul2 := mul_le_mul_of_nonneg_left hmmZ (by norm_num : (0:ℤ)≤13)
    nlinarith only [hbound,hNqZ,hmul,hmul2]
  have hsub : (((S∩Finset.Icc (L:ℤ) (R:ℤ)).card-1:ℕ):ℤ)=
      ((S∩Finset.Icc (L:ℤ) (R:ℤ)).card:ℤ)-1 := by omega
  have hspanN : b.toNat=a.toNat+d.toNat*((S∩Finset.Icc (L:ℤ) (R:ℤ)).card-1) := by
    have hh : (b.toNat:ℤ)=(a.toNat:ℤ)+(d.toNat:ℤ)*
        (((S∩Finset.Icc (L:ℤ) (R:ℤ)).card-1:ℕ):ℤ) := by
      rw [haCast,hbCast,hdCast,hsub]
      dsimp only [a,b]
      linarith only [hspan]
    exact_mod_cast hh
  have ha' : 1≤a.toNat-L+1 := by omega
  have hb' : b.toNat-L+1≤M := by dsimp only [M];omega
  have hspan' : b.toNat-L+1=(a.toNat-L+1)+d.toNat*((S∩Finset.Icc (L:ℤ) (R:ℤ)).card-1) := by omega
  obtain ⟨k,hk,hkd,hau,hub,hdiv⟩ := Ceil13Fringe116.grid_anchor_cover M
    (a.toNat-L+1) (b.toNat-L+1) d.toNat (S∩Finset.Icc (L:ℤ) (R:ℤ)).card
    hM ha' hb' (by omega) (by omega) hspan' hm
  have haShift : ((a.toNat-L+1:ℕ):ℤ)=a-(L:ℤ)+1 := by omega
  have hbShift : ((b.toNat-L+1:ℕ):ℤ)=b-(L:ℤ)+1 := by omega
  simp only [haShift,hbShift,hdCast] at hau hub hdiv
  have hkdZ : (k.1:ℤ)=d := by rw [hkd,hdCast]
  have hau' : a≤Origin M (L:ℤ) k := by dsimp only [Origin];linarith only [hau]
  have hub' : Origin M (L:ℤ) k+d≤b := by dsimp only [Origin];linarith only [hub]
  have hdiv' : d∣Origin M (L:ℤ) k-a := by
    have he : Origin M (L:ℤ) k-a=Ceil13Fringe116.Origin M k-(a-(L:ℤ)+1) := by dsimp only [Origin];ring
    rw [he]
    exact hdiv
  have huS : Origin M (L:ℤ) k∈S∩Finset.Icc (L:ℤ) (R:ℤ) :=
    apAt_fill hAP haS hbS hau' (by linarith only [hub',hd]) hdiv'
  have hvS : Origin M (L:ℤ) k+d∈S∩Finset.Icc (L:ℤ) (R:ℤ) :=
    apAt_fill hAP haS hbS (by linarith only [hau',hd]) hub' (by
      have hh := Int.dvd_add hdiv' (dvd_refl d)
      convert hh using 1
      ring)
  refine ⟨k,hk,?_,huS,?_⟩
  · rw [hkdZ];exact apAt_rebase hAP huS
  · simpa only [hkdZ] using hvS

def Aligned (K : Finset ℤ→Key) (M : ℕ) (L : ℤ) (S : Finset ℤ) : Prop :=
  ∀y∈S,((K S).1:ℤ)∣y-Origin M L (K S)

theorem residue_dvd {M : ℕ} {L : ℤ} {k : Key} {y : ℤ}
    (h : (k.1:ℤ)∣y-Origin M L k) : (k.1:ℤ)∣(y-(L-1))-(k.2.1:ℤ) := by
  have hh : (k.1:ℤ)∣(y-(L-1))-Ceil13Fringe116.Origin M k := by
    convert h using 1
    dsimp only [Origin]
    ring
  exact Ceil13Fringe116.residue_dvd hh

theorem actual_aligned_private {N M : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (K : Finset ℤ→Key) (hlegal : Legal (Ground N) E) (hbad : ∀ S∈E,¬IsAP S)
    (hanchor : ∀ S∈E,HasAnchor M L R (K S) S) :
    ∀ S∈E.filter (Aligned K M L),∃ y,y∈S ∧ y∉Finset.Icc L R ∧
      ∀ T∈E.filter (Aligned K M L),K T=K S → T≠S → y∉T := by
  let A := E.filter (Aligned K M L)
  intro S hS
  let C := A.filter (fun T=>K T=K S)
  have hCS : S∈C := Finset.mem_filter.mpr ⟨hS,rfl⟩
  have hCE : C⊆E := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hc : ∀ T∈C,HasAnchor M L R (K S) T := by
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

theorem actual_aligned_count {N M : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (K : Finset ℤ→Key) (hlegal : Legal (Ground N) E)
    (hbad : ∀ S∈E,¬IsAP S)
    (hkeys : ∀ S∈E,K S∈Keys)
    (hanchor : ∀ S∈E,HasAnchor M L R (K S) S) :
    (E.filter (Aligned K M L)).card≤35*(Ground N\Finset.Icc L R).card := by
  let A := E.filter (Aligned K M L)
  have hex := actual_aligned_private K hlegal hbad hanchor
  choose Y hY using hex
  have hshort : ∀ S∈A,(⟨(K S).1,(K S).2.2⟩:Σ _d:ℕ,ℕ)∈ShortKeys := by
    intro S hS
    obtain ⟨hd,hrj⟩ := Finset.mem_sigma.mp (hkeys S (Finset.mem_filter.mp hS).1)
    have hj := (Finset.mem_product.mp hrj).2
    apply Finset.mem_sigma.mpr
    exact ⟨hd,hj⟩
  have hc : A.card≤((ShortKeys).product (Ground N\Finset.Icc L R)).card := by
    apply Finset.card_le_card_of_injective (f:=fun S:A=>
      (⟨(⟨(K S.val).1,(K S.val).2.2⟩,Y S.val S.property),Finset.mem_product.mpr
        ⟨hshort S.val S.property,Finset.mem_sdiff.mpr
          ⟨hlegal.1 S.val (Finset.mem_filter.mp S.property).1 (hY S.val S.property).1,
            (hY S.val S.property).2.1⟩⟩⟩ : ↥((ShortKeys).product (Ground N\Finset.Icc L R))))
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
    have hAS : Aligned K M L S.val := (Finset.mem_filter.mp S.property).2
    have hAT : Aligned K M L T.val := (Finset.mem_filter.mp T.property).2
    have hresS := residue_dvd (hAS _ (hY S.val S.property).1)
    have hresT := residue_dvd (hAT _ (hY T.val T.property).1)
    rw [←hy,←hd] at hresT
    have hrt' : 1≤(K T.val).2.1 ∧ (K T.val).2.1≤(K S.val).1 := by omega
    have hrho := JointFringe44.bounded_residue_eq (by have hh := (Finset.mem_Icc.mp hds).1;omega) hrs hrt' hresS hresT
    have hkEq : K S.val=K T.val := Sigma.ext hd (heq_of_eq (Prod.ext hrho hj))
    have hyT : Y S.val S.property∈T.val := by rw [hy];exact (hY T.val T.property).1
    exact (hY S.val S.property).2.2 T.val T.property hkEq.symm (Ne.symm hne) hyT
  have he := Finset.card_product (ShortKeys) (Ground N\Finset.Icc L R)
  exact hc.trans_eq (he.trans (by rw [short_keys_card]))



theorem actual_off_point_capacity13 {N L R : ℕ} {F : Finset (Finset ℤ)}
    (d a : Finset ℤ→ℤ) (y : ℤ)
    (hI : 13^3≤(Finset.Icc (L:ℤ) (R:ℤ)).card)
    (hlegal : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S) (a S) (S∩Finset.Icc (L:ℤ) (R:ℤ)))
    (hlong : ∀S∈F,(Finset.Icc (L:ℤ) (R:ℤ)).card<13*(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    (OffResidue44.OffPoint F d a y).card≤13 := by
  apply TracePacking43.actual_long_trace_capacity_cubic (Finset.Icc (L:ℤ) (R:ℤ))
    (OffResidue44.OffPoint F d a y) (fun S=>S∩Finset.Icc (L:ℤ) (R:ℤ)) 13 (by decide) hI
  · intro S hS
    exact Finset.inter_subset_right
  · intro S hS
    exact hlong S (Finset.mem_filter.mp hS).1
  · intro S hS T hT hne
    obtain ⟨hSF,hyS,hoff⟩ := Finset.mem_filter.mp hS
    obtain ⟨hTF,hyT,_hoffT⟩ := Finset.mem_filter.mp hT
    exact OffResidue44.off_point_trace_inter_card (htrace S hSF)
      (hlegal.2 S hSF T hTF hne) hyS hyT hoff

theorem actual_off_residue_count13 {N L R : ℕ} {F : Finset (Finset ℤ)}
    (d a : Finset ℤ→ℤ) (hI : 13^3≤(Finset.Icc (L:ℤ) (R:ℤ)).card)
    (hlegal : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S) (a S) (S∩Finset.Icc (L:ℤ) (R:ℤ)))
    (hlong : ∀S∈F,(Finset.Icc (L:ℤ) (R:ℤ)).card<13*(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    (OffResidue44.OffMembers F d a).card≤13*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  have hcover : OffResidue44.OffMembers F d a⊆
      (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).biUnion (OffResidue44.OffPoint F d a) := by
    intro S hS
    obtain ⟨hSF,y,hyS,hoff⟩ := Finset.mem_filter.mp hS
    have hyI : y∉Finset.Icc (L:ℤ) (R:ℤ) := by
      intro hyI
      exact hoff (OffResidue44.origin_dvd (htrace S hSF) (Finset.mem_inter.mpr ⟨hyS,hyI⟩))
    exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_sdiff.mpr ⟨hlegal.1 S hSF hyS,hyI⟩,
      Finset.mem_filter.mpr ⟨hSF,hyS,hoff⟩⟩
  calc
    _≤((Ground N\Finset.Icc (L:ℤ) (R:ℤ)).biUnion (OffResidue44.OffPoint F d a)).card := Finset.card_le_card hcover
    _≤∑y∈Ground N\Finset.Icc (L:ℤ) (R:ℤ),(OffResidue44.OffPoint F d a y).card := Finset.card_biUnion_le
    _≤∑_y∈Ground N\Finset.Icc (L:ℤ) (R:ℤ),13 := Finset.sum_le_sum (by
      intro y hy
      exact actual_off_point_capacity13 d a y hI hlegal htrace hlong)
    _=13*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by simp [Nat.mul_comm]

theorem actual_long_trace_fringe_bound48 {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (_hRN : R≤N) (hM : 13^3≤R-L+1)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hm : ∀S∈E,(R-L+1)/13+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    E.card≤48*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  obtain ⟨H,hHF,hHAP,hKH⟩ := hcore
  let M := R-L+1
  have hI : 13^3≤(Finset.Icc (L:ℤ) (R:ℤ)).card := by
    rwa [Relative13Fringe116.interval_card hLR]
  have hpair : ∀S∈E,IsAP (S∩H) := by
    intro S hS
    exact hlegal.2 S (hEF hS) H hHF (by intro hh;exact hbad S hS (hh ▸ hHAP))
  have hcover : ∀S∈E,∃k∈Relative13Fringe116.Keys,
      Relative13Fringe116.HasAnchor M (L:ℤ) (R:ℤ) k S := by
    intro S hS
    exact Relative13Fringe116.actual_trace_anchor hL hLR (by norm_num at hM;omega)
      (hpair S hS) hKH (hm S hS)
  let K : Finset ℤ→Relative13Fringe116.Key :=
    fun S=>if h:S∈E then Classical.choose (hcover S h) else ⟨1,1,1⟩
  have hK : ∀S∈E,K S∈Relative13Fringe116.Keys ∧
      Relative13Fringe116.HasAnchor M (L:ℤ) (R:ℤ) (K S) S := by
    intro S hS
    simpa only [K,dif_pos hS] using Classical.choose_spec (hcover S hS)
  have hELegal : Legal (Ground N) E := ⟨fun S hS=>hlegal.1 S (hEF hS),
    fun S hS T hT hn=>hlegal.2 S (hEF hS) T (hEF hT) hn⟩
  let d : Finset ℤ→ℤ := fun S=>(K S).1
  let a : Finset ℤ→ℤ := fun S=>Relative13Fringe116.Origin M (L:ℤ) (K S)
  have hlong : ∀S∈E,(Finset.Icc (L:ℤ) (R:ℤ)).card<
      13*(S∩Finset.Icc (L:ℤ) (R:ℤ)).card := by
    intro S hS
    have hh := Nat.lt_mul_div_succ M (by decide : 0<13)
    have hhm := hm S hS
    rw [Relative13Fringe116.interval_card hLR]
    change M<13*(S∩Finset.Icc (L:ℤ) (R:ℤ)).card
    omega
  have ho := Relative13Fringe116.actual_off_residue_count13 d a hI hELegal
    (fun S hS=>(hK S hS).2.1) hlong
  have ha := Relative13Fringe116.actual_aligned_count K hELegal hbad
    (fun S hS=>(hK S hS).1) (fun S hS=>(hK S hS).2)
  have he : E.filter (fun S=>¬Relative13Fringe116.Aligned K M (L:ℤ) S)=
      OffResidue44.OffMembers E d a := by
    ext S
    simp [Relative13Fringe116.Aligned,OffResidue44.OffMembers,d,a]
  have hc := Finset.card_filter_add_card_filter_not (s:=E) (Relative13Fringe116.Aligned K M (L:ℤ))
  rw [he] at hc
  nlinarith only [ha,ho,hc]


#print axioms short_keys_card
#print axioms interval_card
#print axioms actual_trace_anchor
#print axioms residue_dvd
#print axioms actual_aligned_private
#print axioms actual_aligned_count
#print axioms actual_off_point_capacity13
#print axioms actual_off_residue_count13
#print axioms actual_long_trace_fringe_bound48
end
end JSP233.Relative13Fringe116
