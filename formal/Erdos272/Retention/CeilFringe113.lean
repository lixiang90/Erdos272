import Erdos272.Retention.JointFringe44

/-! Actual ceil-grid preceding anchors, with the real interval as the off pool. -/
namespace JSP233.CeilFringe113
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

abbrev Key := JointFringe44.Key
def Keys : Finset Key :=
  (Finset.Icc 1 14).sigma (fun d=>(Finset.Icc 1 d).product (Finset.Icc 1 (14/d)))
def ShortKeys : Finset (Σ _d:ℕ,ℕ) :=
  (Finset.Icc 1 14).sigma (fun d=>Finset.Icc 1 (14/d))
def Origin (N : ℕ) (k : Key) : ℤ :=
  (k.2.1:ℤ)+((k.2.2:ℤ)*((N+14)/15:ℕ)-1)*(k.1:ℤ)
def HasAnchor (N : ℕ) (L R : ℤ) (k : Key) (S : Finset ℤ) : Prop :=
  APAt (k.1:ℤ) (Origin N k) (S∩Finset.Icc L R) ∧
    Origin N k∈S∩Finset.Icc L R ∧ Origin N k+(k.1:ℤ)∈S∩Finset.Icc L R

theorem short_keys_card : ShortKeys.card=41 := by
  norm_num [ShortKeys,Finset.card_sigma,Finset.sum_Icc_succ_top]

theorem grid_anchor_cover (N a b d m : ℕ) (hN : 225≤N)
    (ha : 1≤a) (hb : b≤N) (hd : 1≤d) (hdr : d≤14)
    (hspan : b=a+d*(m-1)) (hm : N/15+1<m) :
    ∃k∈Keys,k.1=d ∧ (a:ℤ)≤Origin N k ∧ Origin N k+(d:ℤ)≤b ∧
      (d:ℤ)∣Origin N k-(a:ℤ) := by
  let q := (N+14)/15
  have hq : 0<q := by dsimp only [q];omega
  have hqN : N≤15*q := by dsimp only [q];omega
  have hqm : q≤m-1 := by dsimp only [q];omega
  let rho := (a-1)%d+1
  let z := (a-1)/d
  let j := z/q+1
  have hr : 1≤rho ∧ rho≤d := by
    have hh := Nat.mod_lt (a-1) (by omega : 0<d)
    dsimp only [rho];omega
  have haz : a=rho+d*z := by
    have hh := Nat.mod_add_div (a-1) d
    dsimp only [rho,z];omega
  have hj : z<j*q ∧ j*q≤z+q := by
    have hh := Nat.mod_add_div z q
    have hl := Nat.mod_lt z hq
    dsimp only [j]
    constructor <;> nlinarith [Nat.zero_le (z%q)]
  let u := rho+j*q*d
  have hau : a+d≤u := by dsimp only [u];nlinarith
  have hub : u≤b := by dsimp only [u];nlinarith
  have hjd : j*d≤14 := by
    by_contra hn
    have hh := Nat.mul_le_mul_left q (show 15≤j*d by omega)
    dsimp only [u] at hub
    nlinarith
  have hjlo : 1≤j := Nat.le_add_left 1 (z/q)
  have hjhi : j≤14/d := (Nat.le_div_iff_mul_le (by omega : 0<d)).mpr hjd
  let k : Key := ⟨d,rho,j⟩
  have hk : k∈Keys := Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd,hdr⟩,
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hr,Finset.mem_Icc.mpr ⟨hjlo,hjhi⟩⟩⟩
  have hpoint : Origin N k=(u:ℤ)-(d:ℤ) := by
    dsimp only [Origin,k,u,q]
    push_cast
    ring
  refine ⟨k,hk,rfl,?_,?_,?_⟩
  · rw [hpoint]
    have hh : (a:ℤ)+(d:ℤ)≤(u:ℤ) := by exact_mod_cast hau
    omega
  · rw [hpoint];omega
  · rw [hpoint]
    refine ⟨((j*q:ℕ):ℤ)-(z:ℤ)-1,?_⟩
    have haZ : (a:ℤ)=(rho:ℤ)+(d:ℤ)*(z:ℤ) := by exact_mod_cast haz
    dsimp only [u]
    push_cast
    nlinarith only [haZ]

theorem actual_trace_anchor (r N : ℕ) (hr : 0<r) (hp : r<15)
    (hN : 225≤N) {S H : Finset ℤ} {L R : ℤ}
    (hS : S⊆Ground N) (hpair : IsAP (S∩H)) (hKH : Finset.Icc L R⊆H)
    (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ)) (hdense : N<r*S.card)
    (hthin : r*15*((Ground N\Finset.Icc L R).card+1)≤(15-r)*N) :
    ∃k∈Keys,HasAnchor N L R k S := by
  obtain ⟨d,a0,hAP,hdr,hm⟩ := FlexibleTrace44.dense_trace_geometry r 15 N hr hp
    hS hpair hKH hL hLR hR hdense hthin
  have hd := hAP.1
  have hcard : 2≤(S∩Finset.Icc L R).card := by omega
  have hne : (S∩Finset.Icc L R).Nonempty := Finset.card_pos.mp (by omega)
  let a := (S∩Finset.Icc L R).min' hne
  let b := (S∩Finset.Icc L R).max' hne
  have haS : a∈S∩Finset.Icc L R := Finset.min'_mem _ hne
  have hbS : b∈S∩Finset.Icc L R := Finset.max'_mem _ hne
  have haK := Finset.mem_Icc.mp (Finset.mem_inter.mp haS).2
  have hbK := Finset.mem_Icc.mp (Finset.mem_inter.mp hbS).2
  have haCast : (a.toNat:ℤ)=a := Int.toNat_of_nonneg (by omega)
  have hbCast : (b.toNat:ℤ)=b := Int.toNat_of_nonneg (by omega)
  have hdCast : (d.toNat:ℤ)=d := Int.toNat_of_nonneg hd.le
  have hspan := apAt_span_eq hAP hne
  have hsub : (((S∩Finset.Icc L R).card-1:ℕ):ℤ)=((S∩Finset.Icc L R).card:ℤ)-1 := by omega
  have hspanN : b.toNat=a.toNat+d.toNat*((S∩Finset.Icc L R).card-1) := by
    have hh : (b.toNat:ℤ)=(a.toNat:ℤ)+(d.toNat:ℤ)*(((S∩Finset.Icc L R).card-1:ℕ):ℤ) := by
      rw [haCast,hbCast,hdCast,hsub]
      dsimp only [a,b]
      linarith only [hspan]
    exact_mod_cast hh
  obtain ⟨k,hk,hkd,hau,hub,hdiv⟩ := grid_anchor_cover N a.toNat b.toNat d.toNat
    (S∩Finset.Icc L R).card hN (by omega) (by omega) (by omega) (by omega) hspanN hm
  have hkdZ : (k.1:ℤ)=d := by rw [hkd,hdCast]
  simp only [haCast,hbCast,hdCast] at hau hub hdiv
  have huS : Origin N k∈S∩Finset.Icc L R := apAt_fill hAP haS hbS hau (by linarith only [hub,hd]) hdiv
  have hvS : Origin N k+d∈S∩Finset.Icc L R := apAt_fill hAP haS hbS (by linarith only [hau,hd]) hub (by
    have hh := Int.dvd_add hdiv (dvd_refl d)
    convert hh using 1
    ring)
  refine ⟨k,hk,?_,huS,?_⟩
  · rw [hkdZ];exact apAt_rebase hAP huS
  · simpa only [hkdZ] using hvS

def Aligned (K : Finset ℤ→Key) (N : ℕ) (S : Finset ℤ) : Prop :=
  ∀y∈S,((K S).1:ℤ)∣y-Origin N (K S)

theorem residue_dvd {N : ℕ} {k : Key} {y : ℤ}
    (h : (k.1:ℤ)∣y-Origin N k) : (k.1:ℤ)∣y-(k.2.1:ℤ) := by
  have hg : (k.1:ℤ)∣Origin N k-(k.2.1:ℤ) := by
    refine ⟨(k.2.2:ℤ)*((N+14)/15:ℕ)-1,?_⟩
    dsimp only [Origin]
    ring
  have hh := Int.dvd_add h hg
  convert hh using 1
  ring

theorem actual_aligned_private {N : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (K : Finset ℤ→Key) (hlegal : Legal (Ground N) E) (hbad : ∀ S∈E,¬IsAP S)
    (hanchor : ∀ S∈E,HasAnchor N L R (K S) S) :
    ∀ S∈E.filter (Aligned K N),∃ y,y∈S ∧ y∉Finset.Icc L R ∧
      ∀ T∈E.filter (Aligned K N),K T=K S → T≠S → y∉T := by
  let A := E.filter (Aligned K N)
  intro S hS
  let C := A.filter (fun T=>K T=K S)
  have hCS : S∈C := Finset.mem_filter.mpr ⟨hS,rfl⟩
  have hCE : C⊆E := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hc : ∀ T∈C,HasAnchor N L R (K S) T := by
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

theorem actual_aligned_count {N : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (K : Finset ℤ→Key) (hlegal : Legal (Ground N) E)
    (hbad : ∀ S∈E,¬IsAP S)
    (hkeys : ∀ S∈E,K S∈Keys)
    (hanchor : ∀ S∈E,HasAnchor N L R (K S) S) :
    (E.filter (Aligned K N)).card≤41*(Ground N\Finset.Icc L R).card := by
  let A := E.filter (Aligned K N)
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
    have hAS : Aligned K N S.val := (Finset.mem_filter.mp S.property).2
    have hAT : Aligned K N T.val := (Finset.mem_filter.mp T.property).2
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


theorem actual_off_point_capacity14 {N L R : ℕ} {F : Finset (Finset ℤ)}
    (d a : Finset ℤ→ℤ) (y : ℤ) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hlarge : 90<L+N-R) (hlegal : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S) (a S) (S∩Finset.Icc (L:ℤ) (R:ℤ)))
    (hlong : ∀S∈F,N/15+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    (OffResidue44.OffPoint F d a y).card≤14 := by
  by_contra hn
  obtain ⟨E,hEF,hEc⟩ := Finset.exists_subset_card_eq (show 15≤(OffResidue44.OffPoint F d a y).card by omega)
  let T := fun S:Finset ℤ=>S∩Finset.Icc (L:ℤ) (R:ℤ)
  have hpair : ∀S∈E,∀U∈E,S≠U→((T S)∩(T U)).card≤1 := by
    intro S hS U hU hne
    obtain ⟨hSF,hyS,hoff⟩ := Finset.mem_filter.mp (hEF hS)
    obtain ⟨hUF,hyU,_hoffU⟩ := Finset.mem_filter.mp (hEF hU)
    exact OffResidue44.off_point_trace_inter_card (htrace S hSF)
      (hlegal.2 S hSF U hUF hne) hyS hyU hoff
  have hs := TracePacking43.trace_sum_bound E T hpair
  have hsub : E.biUnion T⊆Finset.Icc (L:ℤ) (R:ℤ) := by
    intro x hx
    obtain ⟨S,_hS,hx⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hx).2
  have hupper := Finset.card_le_card hsub
  have hsum : ∑S∈E,(N/15+2)≤∑S∈E,(T S).card := by
    apply Finset.sum_le_sum
    intro S hS
    exact hlong S (Finset.mem_filter.mp (hEF hS)).1
  have hI : (Finset.Icc (L:ℤ) (R:ℤ)).card=R-L+1 := by
    simp only [Int.card_Icc]
    omega
  simp only [Finset.sum_const,nsmul_eq_mul,hEc] at hsum
  rw [hEc] at hs
  norm_num [Nat.choose] at hs
  rw [hI] at hupper
  have hrem := Nat.mod_add_div N 15
  have hmod := Nat.mod_lt N (by decide : 0<15)
  omega

theorem actual_off_residue_count14 {N L R : ℕ} {F : Finset (Finset ℤ)}
    (d a : Finset ℤ→ℤ) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hlarge : 90<L+N-R) (hlegal : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S) (a S) (S∩Finset.Icc (L:ℤ) (R:ℤ)))
    (hlong : ∀S∈F,N/15+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    (OffResidue44.OffMembers F d a).card≤14*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
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
    _≤∑_y∈Ground N\Finset.Icc (L:ℤ) (R:ℤ),14 := Finset.sum_le_sum (by
      intro y hy
      exact actual_off_point_capacity14 d a y hL hLR hRN hlarge hlegal htrace hlong)
    _=14*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by simp [Nat.mul_comm]

theorem actual_dense_fringe_bound55 {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 225≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hlarge : 90<L+N-R)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hdense : ∀S∈E,N<11*S.card)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hgeometry : 165*(L+N-R)≤4*N) :
    E.card≤55*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  obtain ⟨H,hHF,hHAP,hKH⟩ := hcore
  have hext := ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
    (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
  have hext' : (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card+1=L+N-R := by omega
  have hthin : 11*15*((Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card+1)≤(15-11)*N := by
    rw [hext'];norm_num;omega
  have hpair : ∀S∈E,IsAP (S∩H) := by
    intro S hS
    exact hlegal.2 S (hEF hS) H hHF (by intro hh;exact hbad S hS (hh ▸ hHAP))
  have hcover : ∀S∈E,∃k∈Keys,HasAnchor N (L:ℤ) (R:ℤ) k S := by
    intro S hS
    exact actual_trace_anchor 11 N (by decide) (by decide) hN (hlegal.1 S (hEF hS))
      (hpair S hS) hKH (by exact_mod_cast hL) (by exact_mod_cast hLR) (by exact_mod_cast hRN)
      (hdense S hS) hthin
  let K : Finset ℤ→Key := fun S=>if h:S∈E then Classical.choose (hcover S h) else ⟨1,1,1⟩
  have hK : ∀S∈E,K S∈Keys ∧ HasAnchor N (L:ℤ) (R:ℤ) (K S) S := by
    intro S hS
    simpa only [K,dif_pos hS] using Classical.choose_spec (hcover S hS)
  have hELegal : Legal (Ground N) E := ⟨fun S hS=>hlegal.1 S (hEF hS),
    fun S hS T hT hn=>hlegal.2 S (hEF hS) T (hEF hT) hn⟩
  let d : Finset ℤ→ℤ := fun S=>(K S).1
  let a : Finset ℤ→ℤ := fun S=>Origin N (K S)
  have hm : ∀S∈E,N/15+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card := by
    intro S hS
    obtain ⟨_d,_a,_hAP,_hdr,hm⟩ := FlexibleTrace44.dense_trace_geometry 11 15 N
      (by decide) (by decide) (hlegal.1 S (hEF hS)) (hpair S hS) hKH
      (by exact_mod_cast hL) (by exact_mod_cast hLR) (by exact_mod_cast hRN) (hdense S hS) hthin
    exact hm
  have ho := actual_off_residue_count14 d a hL hLR hRN hlarge hELegal (fun S hS=>(hK S hS).2.1) hm
  have ha := actual_aligned_count K hELegal hbad (fun S hS=>(hK S hS).1) (fun S hS=>(hK S hS).2)
  have he : E.filter (fun S=>¬Aligned K N S)=OffResidue44.OffMembers E d a := by
    ext S
    simp [Aligned,OffResidue44.OffMembers,d,a]
  have hc := Finset.card_filter_add_card_filter_not (s:=E) (Aligned K N)
  rw [he] at hc
  nlinarith only [ha,ho,hc]

#print axioms short_keys_card
#print axioms grid_anchor_cover
#print axioms actual_trace_anchor
#print axioms residue_dvd
#print axioms actual_aligned_private
#print axioms actual_aligned_count
#print axioms actual_off_point_capacity14
#print axioms actual_off_residue_count14
#print axioms actual_dense_fringe_bound55
end
end JSP233.CeilFringe113
