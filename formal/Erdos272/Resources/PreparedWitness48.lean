import Erdos272.Counting.OneSided47

/-! Actual preferred witnesses and cropped traces after the actual one-sided envelope. -/
namespace JSP233.PreparedWitness48
open StarCompletion APGeometry LongTerminal35 WitnessInterval43 RestrictedWitness44
open PrivatePairExistence DenseDeletion40 FamilyReflect43
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

def Consecutive (S : Finset ℤ) (u v : ℤ) : Prop :=
  u∈S ∧ v∈S ∧ u<v ∧ ∀ z∈S,u<z→z<v→False

def HasMiddleWitness (S : Finset ℤ) (c L R : ℤ) : Prop :=
  ∃ Q,IntrinsicPair c S Q ∧ ∃ z∈Q,L≤z ∧ z≤R

def HighMembers (F : Finset (Finset ℤ)) (c L : ℤ) : Finset (Finset ℤ) :=
  (CrookedMembers F).filter (fun S=>∃ Q,IntrinsicPair c S Q ∧ ∃ z∈Q,L≤z)

def BoundaryWitness (S : Finset ℤ) (c L : ℤ) : Prop :=
  ∃ Q,IntrinsicPair c S Q ∧ L∈Q

def PreparedCrooked (F : Finset (Finset ℤ)) (c L : ℤ) : Finset (Finset ℤ) :=
  (HighMembers F c L).filter (fun S=>¬BoundaryWitness S c L)

theorem consecutive_subset {S A : Finset ℤ} {u v : ℤ}
    (hc : Consecutive S u v) (hAS : A⊆S) (hu : u∈A) (hv : v∈A) :
    Consecutive A u v :=
  ⟨hu,hv,hc.2.2.1,fun z hz=>hc.2.2.2 z (hAS hz)⟩

theorem actual_consecutive_step {S A : Finset ℤ} {u v d p : ℤ}
    (hc : Consecutive S u v) (hAS : A⊆S) (hp : APAt d p A)
    (hu : u∈A) (hv : v∈A) : d=v-u := by
  have hd : 0<d := hp.1
  have huv : u<v := hc.2.2.1
  have hdiv := apAt_dvd_sub hp hu hv
  have hle : d≤v-u := Int.le_of_dvd (by omega : 0<v-u) hdiv
  have hm : u+d∈A := apAt_fill hp hu hv (by omega) (by omega) (by simp)
  by_contra hn
  exact hc.2.2.2 (u+d) (hAS hm) (by omega) (by omega)

theorem actual_AP_union_consecutive {S A B : Finset ℤ} {u v : ℤ}
    (hc : Consecutive S u v) (hAS : A⊆S) (hBS : B⊆S)
    (hA : IsAP A) (hB : IsAP B) (huA : u∈A) (hvA : v∈A)
    (huB : u∈B) (hvB : v∈B) : IsAP (A∪B) := by
  obtain ⟨d,p,hp,_⟩ := (isAP_iff_exists_APAt A).mp hA
  obtain ⟨e,q,hq,_⟩ := (isAP_iff_exists_APAt B).mp hB
  have hd := actual_consecutive_step hc hAS hp huA hvA
  have he := actual_consecutive_step hc hBS hq huB hvB
  have hp' : APAt (v-u) u A := by rw [←hd];exact apAt_rebase hp huA
  have hq' : APAt (v-u) u B := by rw [←he];exact apAt_rebase hq huB
  have hh : APAt (v-u) u (A∪B) := by
    simpa only [APAt,Finset.mem_union] using
      PrivateUnion.union_APAt (v-u) u (fun x=>x∈A) (fun x=>x∈B) hp' hq' huA huB
  exact (isAP_iff_exists_APAt _).mpr ⟨v-u,u,hh,Finset.mem_union_left _ huA⟩

theorem cover_of_not_intrinsic {S Q : Finset ℤ} {c : ℤ}
    (hq : Q.card=2) (hc : c∉Q) (hQS : Q⊆S) (hn : ¬IntrinsicPair c S Q) :
    Cover S (insert c Q) := by
  by_contra hnot
  exact hn ⟨hq,hc,hQS,hnot⟩

theorem cover_mono {S A B : Finset ℤ} (hB : Cover S B) (hAB : A⊆B) : Cover S A := by
  obtain ⟨U,hU,hBU,hUS⟩ := hB
  exact ⟨U,hU,hAB.trans hBU,hUS⟩

theorem cover_union_consecutive {S A B : Finset ℤ} {u v : ℤ}
    (hc : Consecutive S u v) (hA : Cover S A) (hB : Cover S B)
    (huA : u∈A) (hvA : v∈A) (huB : u∈B) (hvB : v∈B) : Cover S (A∪B) := by
  obtain ⟨U,hU,hAU,hUS⟩ := hA
  obtain ⟨V,hV,hBV,hVS⟩ := hB
  exact ⟨U∪V,actual_AP_union_consecutive hc hUS hVS hU hV
    (hAU huA) (hAU hvA) (hBV huB) (hBV hvB),
    Finset.union_subset_union hAU hBV,Finset.union_subset hUS hVS⟩

theorem actual_intrinsic_redirect_neighbor {S : Finset ℤ} {c z x y : ℤ}
    (hn : Consecutive S c z ∨ Consecutive S z c) (hw : IntrinsicPair c S {x,y}) :
    IntrinsicPair c S {z,x} ∨ IntrinsicPair c S {z,y} := by
  by_cases hzx : z=x
  · exact Or.inr (by simpa only [hzx] using hw)
  by_cases hzy : z=y
  · exact Or.inl (by simpa only [hzy,Finset.pair_comm] using hw)
  have hzS : z∈S := by rcases hn with hh|hh;exact hh.2.1;exact hh.1
  have hzc : z≠c := by rcases hn with hh|hh;have ht:=hh.2.2.1;omega;have ht:=hh.2.2.1;omega
  have hxS : x∈S := hw.2.2.1 (by simp)
  have hyS : y∈S := hw.2.2.1 (by simp)
  have hxc : x≠c := by intro he;exact hw.2.1 (by simp [←he])
  have hyc : y≠c := by intro he;exact hw.2.1 (by simp [←he])
  by_contra hnot
  have hX := cover_of_not_intrinsic (by simp [hzx] : ({z,x}:Finset ℤ).card=2)
    (by simp [Ne.symm hzc,Ne.symm hxc] : c∉({z,x}:Finset ℤ))
    (Finset.insert_subset_iff.mpr ⟨hzS,Finset.singleton_subset_iff.mpr hxS⟩)
    (fun hh=>hnot (Or.inl hh))
  have hY := cover_of_not_intrinsic (by simp [hzy] : ({z,y}:Finset ℤ).card=2)
    (by simp [Ne.symm hzc,Ne.symm hyc] : c∉({z,y}:Finset ℤ))
    (Finset.insert_subset_iff.mpr ⟨hzS,Finset.singleton_subset_iff.mpr hyS⟩)
    (fun hh=>hnot (Or.inr hh))
  have hU : Cover S ((insert c {z,x})∪(insert c {z,y})) := by
    rcases hn with hh|hh
    · exact cover_union_consecutive hh hX hY (by simp) (by simp) (by simp) (by simp)
    · exact cover_union_consecutive hh hX hY (by simp) (by simp) (by simp) (by simp)
  exact hw.2.2.2 (cover_mono hU (by intro t ht;simp only [Finset.mem_insert,Finset.mem_singleton] at ht;rcases ht with rfl|rfl|rfl <;>simp))

theorem actual_root_neighbor_le {S : Finset ℤ} {c t R : ℤ}
    (hc : c∈S) (ht : t∈S) (htc : t≠c) (hcR : c≤R) (htR : t≤R) :
    ∃ z,z≤R ∧ (Consecutive S c z ∨ Consecutive S z c) := by
  by_cases htc' : t<c
  · let A := S.filter (fun x=>x<c)
    have hA : A.Nonempty := ⟨t,Finset.mem_filter.mpr ⟨ht,htc'⟩⟩
    let z := A.max' hA
    obtain ⟨hzS,hzc⟩ := Finset.mem_filter.mp (Finset.max'_mem A hA)
    refine ⟨z,by omega,Or.inr ⟨hzS,hc,hzc,?_⟩⟩
    intro x hx hzx hxc
    have hh : x≤z := Finset.le_max' A x (Finset.mem_filter.mpr ⟨hx,hxc⟩)
    omega
  · let A := S.filter (fun x=>c<x)
    have hct : c<t := by omega
    have hA : A.Nonempty := ⟨t,Finset.mem_filter.mpr ⟨ht,hct⟩⟩
    let z := A.min' hA
    obtain ⟨hzS,hcz⟩ := Finset.mem_filter.mp (Finset.min'_mem A hA)
    have hzt : z≤t := Finset.min'_le A t (Finset.mem_filter.mpr ⟨ht,hct⟩)
    refine ⟨z,by omega,Or.inl ⟨hc,hzS,hcz,?_⟩⟩
    intro x hx hcx hxz
    have hh : z≤x := Finset.min'_le A x (Finset.mem_filter.mpr ⟨hx,hcx⟩)
    omega

theorem actual_witness_high_reaches_low {S Q : Finset ℤ} {c t L R : ℤ}
    (hc : c∈S) (ht : t∈S) (htc : t≠c) (hcR : c≤R) (htR : t≤R) (hLR : L≤R)
    (hw : IntrinsicPair c S Q) (hhigh : ∃ x∈Q,L≤x) :
    ∃ W,IntrinsicPair c S W ∧ (∃ x∈W,L≤x) ∧ ∃ y∈W,y≤R := by
  by_cases hl : ∃ y∈Q,y≤R
  · exact ⟨Q,hw,hhigh,hl⟩
  obtain ⟨x,y,_hxy,hrep⟩ := Finset.card_eq_two.mp hw.1
  have hRx : R<x := by by_contra hn;exact hl ⟨x,by simp [hrep],by omega⟩
  have hRy : R<y := by by_contra hn;exact hl ⟨y,by simp [hrep],by omega⟩
  obtain ⟨z,hzR,hn⟩ := actual_root_neighbor_le hc ht htc hcR htR
  have hp : IntrinsicPair c S {x,y} := by simpa only [hrep] using hw
  rcases actual_intrinsic_redirect_neighbor hn hp with hx|hy
  · exact ⟨{z,x},hx,⟨x,by simp,by omega⟩,z,by simp,hzR⟩
  · exact ⟨{z,y},hy,⟨y,by simp,by omega⟩,z,by simp,hzR⟩

theorem actual_pair_eq_of_card_two {Q : Finset ℤ} {x y : ℤ}
    (hc : Q.card=2) (hx : x∈Q) (hy : y∈Q) (hxy : x≠y) : Q={x,y} := by
  have hs : ({x,y}:Finset ℤ)⊆Q := Finset.insert_subset_iff.mpr ⟨hx,Finset.singleton_subset_iff.mpr hy⟩
  exact (Finset.eq_of_subset_of_card_le hs (by simp [hc,hxy])).symm

theorem actual_preferred_witness {S : Finset ℤ} {c L R : ℤ} (hLR : L≤R)
    (hreach : ∃ W,IntrinsicPair c S W ∧ (∃ x∈W,L≤x) ∧ ∃ y∈W,y≤R) :
    ∃ x p:ℤ,IntrinsicPair c S {x,p} ∧ L≤p ∧
      (p≤R ∨ (x<L ∧ R<p ∧ ¬HasMiddleWitness S c L R ∧
        ∀ u v:ℤ,u<L→R<v→IntrinsicPair c S {u,v}→p-x≤v-u)) := by
  by_cases hm : HasMiddleWitness S c L R
  · obtain ⟨Q,hw,p,hp,hLp,hpR⟩ := hm
    obtain ⟨a,b,_hab,hrep⟩ := Finset.card_eq_two.mp hw.1
    rw [hrep] at hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with hpa|hpb
    · exact ⟨b,p,by simpa only [hrep,hpa,Finset.pair_comm] using hw,hLp,Or.inl hpR⟩
    · exact ⟨a,p,by simpa only [hrep,hpb] using hw,hLp,Or.inl hpR⟩
  · obtain ⟨W,hw,⟨p,hp,hLp⟩,x,hx,hxR⟩ := hreach
    have hRp : R<p := by by_contra hn;exact hm ⟨W,hw,p,hp,hLp,by omega⟩
    have hxL : x<L := by by_contra hn;exact hm ⟨W,hw,x,hx,by omega,hxR⟩
    have hrep := actual_pair_eq_of_card_two hw.1 hx hp (by omega : x≠p)
    have hpW : IntrinsicPair c S {x,p} := by simpa only [hrep] using hw
    let C := (S.product S).filter (fun z:ℤ×ℤ=>z.1<L ∧ R<z.2 ∧ IntrinsicPair c S {z.1,z.2})
    have hC : C.Nonempty := ⟨(x,p),Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hw.2.2.1 hx,hw.2.2.1 hp⟩,hxL,hRp,hpW⟩⟩
    obtain ⟨z,hz,hmin⟩ := Finset.exists_min_image C (fun z:ℤ×ℤ=>z.2-z.1) hC
    obtain ⟨_,hzL,hRz,hwz⟩ := Finset.mem_filter.mp hz
    refine ⟨z.1,z.2,hwz,by omega,Or.inr ⟨hzL,hRz,hm,?_⟩⟩
    intro u v hu hv huv
    exact hmin (u,v) (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨huv.2.2.1 (by simp),huv.2.2.1 (by simp)⟩,hu,hv,huv⟩)

theorem actual_consecutive_across_cut {S : Finset ℤ} {R x y : ℤ}
    (hx : x∈S) (hy : y∈S) (hxR : x≤R) (hRy : R<y) :
    ∃ b a,Consecutive S b a ∧ x≤b ∧ b≤R ∧ R<a ∧ a≤y := by
  let B := S.filter (fun z=>z≤R)
  let A := S.filter (fun z=>R<z)
  have hxB : x∈B := Finset.mem_filter.mpr ⟨hx,hxR⟩
  have hyA : y∈A := Finset.mem_filter.mpr ⟨hy,hRy⟩
  have hB : B.Nonempty := ⟨x,hxB⟩
  have hA : A.Nonempty := ⟨y,hyA⟩
  let b := B.max' hB
  let a := A.min' hA
  obtain ⟨hbS,hbR⟩ := Finset.mem_filter.mp (Finset.max'_mem B hB)
  obtain ⟨haS,hRa⟩ := Finset.mem_filter.mp (Finset.min'_mem A hA)
  refine ⟨b,a,⟨hbS,haS,by omega,?_⟩,Finset.le_max' B x hxB,hbR,hRa,Finset.min'_le A y hyA⟩
  intro z hz hbz hza
  by_cases hzR : z≤R
  · have hh : z≤b := Finset.le_max' B z (Finset.mem_filter.mpr ⟨hz,hzR⟩)
    omega
  · have hh : a≤z := Finset.min'_le A z (Finset.mem_filter.mpr ⟨hz,by omega⟩)
    omega

theorem actual_consecutive_crop_card {S : Finset ℤ} {x y : ℤ}
    (hc : Consecutive S x y) : (S∩Finset.Icc x y).card≤2 := by
  have hs : S∩Finset.Icc x y⊆({x,y}:Finset ℤ) := by
    intro z hz
    obtain ⟨hzS,hzI⟩ := Finset.mem_inter.mp hz
    obtain ⟨hxz,hzy⟩ := Finset.mem_Icc.mp hzI
    by_cases hx : z=x
    · simp [hx]
    by_cases hy : z=y
    · simp [hy]
    exact False.elim (hc.2.2.2 z hzS (by omega) (by omega))
  have hh := Finset.card_le_card hs
  simpa only [Finset.card_pair hc.2.2.1.ne] using hh

theorem actual_preferred_AP_crop_card {S : Finset ℤ} {c x p L R : ℤ}
    (hcx : c<x) (hxL : x<L) (hLR : L≤R) (hRp : R<p)
    (hw : IntrinsicPair c S {x,p}) (hnoMiddle : ¬HasMiddleWitness S c L R)
    (hminimum : ∀ u v:ℤ,u<L→R<v→IntrinsicPair c S {u,v}→p-x≤v-u)
    (hAP : IsAP (S∩Finset.Icc x p)) : (S∩Finset.Icc x p).card≤2 := by
  by_contra hsize
  have hxS : x∈S := hw.2.2.1 (by simp)
  have hpS : p∈S := hw.2.2.1 (by simp)
  obtain ⟨b,a,hcon,hxb,hbR,hRa,hap⟩ := actual_consecutive_across_cut hxS hpS (by omega : x≤R) hRp
  have hends : b≠x ∨ a≠p := by
    by_contra hn
    have hb : b=x := by by_contra hh;exact hn (Or.inl hh)
    have ha : a=p := by by_contra hh;exact hn (Or.inr hh)
    exact hsize (actual_consecutive_crop_card (by simpa only [hb,ha] using hcon))
  have hshort : a-b<p-x := by rcases hends with hh|hh <;>omega
  have hnoBA : ¬IntrinsicPair c S {b,a} := by
    intro hBA
    by_cases hLb : L≤b
    · exact hnoMiddle ⟨{b,a},hBA,b,by simp,hLb,hbR⟩
    · have hh := hminimum b a (by omega) hRa hBA
      omega
  have hcBA : c∉({b,a}:Finset ℤ) := by simp;constructor <;>omega
  have hcover := cover_of_not_intrinsic (by simp [hcon.2.2.1.ne] : ({b,a}:Finset ℤ).card=2)
    hcBA (Finset.insert_subset_iff.mpr ⟨hcon.1,Finset.singleton_subset_iff.mpr hcon.2.1⟩) hnoBA
  obtain ⟨U,hUAP,hCU,hUS⟩ := hcover
  let C := S∩Finset.Icc x p
  have hbC : b∈C := Finset.mem_inter.mpr ⟨hcon.1,Finset.mem_Icc.mpr ⟨hxb,by omega⟩⟩
  have haC : a∈C := Finset.mem_inter.mpr ⟨hcon.2.1,Finset.mem_Icc.mpr ⟨by omega,hap⟩⟩
  have hAPunion : IsAP (U∪C) := actual_AP_union_consecutive hcon hUS Finset.inter_subset_left
    hUAP hAP (hCU (by simp)) (hCU (by simp)) hbC haC
  apply hw.2.2.2
  refine ⟨U∪C,hAPunion,?_,Finset.union_subset hUS Finset.inter_subset_left⟩
  intro z hz
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl|rfl|rfl
  · exact Finset.mem_union_left _ (hCU (by simp))
  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxS,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩)
  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hpS,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩⟩)

theorem actual_preferred_crop_dichotomy {S : Finset ℤ} {c x p L R : ℤ}
    (hcx : c<x) (hxL : x<L) (hLR : L≤R) (hRp : R<p)
    (hw : IntrinsicPair c S {x,p}) (hnoMiddle : ¬HasMiddleWitness S c L R)
    (hminimum : ∀ u v:ℤ,u<L→R<v→IntrinsicPair c S {u,v}→p-x≤v-u) :
    S∩Finset.Icc x p={x,p} ∨ ¬IsAP (S∩Finset.Icc x p) := by
  by_cases hbad : ¬IsAP (S∩Finset.Icc x p)
  · exact Or.inr hbad
  · left
    have hcard := actual_preferred_AP_crop_card hcx hxL hLR hRp hw hnoMiddle hminimum (of_not_not hbad)
    have hs : ({x,p}:Finset ℤ)⊆S∩Finset.Icc x p := by
      refine Finset.insert_subset_iff.mpr ⟨?_,Finset.singleton_subset_iff.mpr ?_⟩
      · exact Finset.mem_inter.mpr ⟨hw.2.2.1 (by simp),Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩
      · exact Finset.mem_inter.mpr ⟨hw.2.2.1 (by simp),Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩⟩
    exact (Finset.eq_of_subset_of_card_le hs (by simpa only [Finset.card_pair (show x≠p by omega)] using hcard)).symm

theorem actual_ordered_preferred_witness {S : Finset ℤ} {c L R : ℤ} (hLR : L≤R)
    (hreach : ∃ W,IntrinsicPair c S W ∧ (∃ x∈W,L≤x) ∧ ∃ y∈W,y≤R)
    (hnoL : ∀ W,IntrinsicPair c S W→L∉W) :
    ∃ x p:ℤ,IntrinsicPair c S {x,p} ∧ x<p ∧ x≤R ∧ L<p ∧ x≠L ∧
      (c<x→x<L→R<p→S∩Finset.Icc x p={x,p} ∨ ¬IsAP (S∩Finset.Icc x p)) := by
  obtain ⟨x,p,hw,hLp,hcases⟩ := actual_preferred_witness hLR hreach
  have hxp : x≠p := by
    intro he
    have hh:=hw.1
    simp only [he,Finset.insert_eq_of_mem (Finset.mem_singleton_self p),Finset.card_singleton] at hh
    omega
  have hpL : L<p := by
    have hh : p≠L := by intro he;apply hnoL {x,p} hw;simp [he]
    omega
  have hxLne : x≠L := by intro he;apply hnoL {x,p} hw;simp [he]
  rcases hcases with hpR|⟨hxL,hRp,hnoMiddle,hminimum⟩
  · by_cases hlt : x<p
    · exact ⟨x,p,hw,hlt,by omega,hpL,hxLne,by intro _ _ h;omega⟩
    · refine ⟨p,x,by simpa only [Finset.pair_comm] using hw,by omega,hpR,by omega,by omega,?_⟩
      intro _ h _
      omega
  · exact ⟨x,p,hw,by omega,by omega,hpL,hxLne,
      fun hcx _ _=>actual_preferred_crop_dichotomy hcx hxL hLR hRp hw hnoMiddle hminimum⟩

theorem actual_division_point_witness_card {N : ℕ} {F C : Finset (Finset ℤ)} {c L : ℤ}
    (hF : Legal (Ground N) F) (hCF : C⊆F) (hc : ∀ S∈C,c∈S)
    (hL : ∀ S∈C,BoundaryWitness S c L) : C.card≤N := by
  let X := {S // S∈C}
  have hex : ∀ S:X,∃ x:ℤ,IntrinsicPair c S.val {L,x} := by
    intro S
    obtain ⟨Q,hw,hLQ⟩ := hL S.val S.property
    obtain ⟨a,b,_hab,hrep⟩ := Finset.card_eq_two.mp hw.1
    rw [hrep] at hLQ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hLQ
    rcases hLQ with hLa|hLb
    · exact ⟨b,by simpa only [hrep,←hLa] using hw⟩
    · exact ⟨a,by simpa only [hrep,←hLb,Finset.pair_comm] using hw⟩
  choose x hx using hex
  have hm : ∀ S:X,x S∈Ground N := fun S=>hF.1 S.val (hCF S.property) ((hx S).2.2.1 (by simp))
  have hi : Function.Injective x := by
    intro S T he
    apply Subtype.ext
    apply actual_intrinsic_member_eq hF (hCF S.property) (hCF T.property)
      (hc S.val S.property) (hc T.val T.property) (hx S)
    rw [he]
    exact (hx T).2.2.1
  have hh := Finset.card_le_card_of_injective (f:=fun S:X=>(⟨x S,hm S⟩:Ground N))
    (by intro S T he;apply hi;exact congrArg Subtype.val he)
  simpa only [Fintype.card_coe,ground_card,X] using hh

theorem actual_no_high_witness_card {N : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ} {c L : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ S∈F,¬IsAP S→c∈S)
    (hP : P∈F) (hcP : c∉P) (hLP : ∀ x∈P,L≤x) :
    (CrookedMembers F\HighMembers F c L).card≤WitnessException (Ground N) c := by
  have hs : CrookedMembers F\HighMembers F c L⊆BadMembers F c P := by
    intro S hS
    obtain ⟨hSC,hn⟩ := Finset.mem_sdiff.mp hS
    obtain ⟨hSF,hbad⟩ := Finset.mem_filter.mp hSC
    have hcS := hroot S hSF hbad
    refine Finset.mem_filter.mpr ⟨hSF,hcS,hbad,actual_avoider_meets_erase hF hSF hP hcS hcP,?_⟩
    intro Q hw
    apply Finset.disjoint_left.mpr
    intro z hzQ hzP
    exact hn (Finset.mem_filter.mpr ⟨hSC,Q,hw,z,hzQ,hLP z hzP⟩)
  exact (Finset.card_le_card hs).trans (actual_restricted_bad_family_bound c P hF)

theorem actual_prepared_crooked_count {N : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ} {c L : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ S∈F,¬IsAP S→c∈S)
    (hP : P∈F) (hcP : c∉P) (hLP : ∀ x∈P,L≤x) :
    (CrookedMembers F).card≤(PreparedCrooked F c L).card+N+WitnessException (Ground N) c := by
  have hbad := actual_no_high_witness_card hF hroot hP hcP hLP
  let D := (HighMembers F c L).filter (fun S=>BoundaryWitness S c L)
  have hDF : D⊆F := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).1
  have hD : D.card≤N := actual_division_point_witness_card hF hDF
    (fun S hS=>hroot S (hDF hS) (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2)
    (fun S hS=>(Finset.mem_filter.mp hS).2)
  have hHsub : HighMembers F c L⊆CrookedMembers F := Finset.filter_subset _ _
  have hp := Finset.card_sdiff_add_card_eq_card hHsub
  have hq := Finset.card_filter_add_card_filter_not (s:=HighMembers F c L) (fun S=>BoundaryWitness S c L)
  change D.card+(PreparedCrooked F c L).card=(HighMembers F c L).card at hq
  omega

theorem actual_prepared_crooked_harmonic {N : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ} {c L : ℤ}
    (hcN : c∈Ground N) (hF : Legal (Ground N) F) (hroot : ∀ S∈F,¬IsAP S→c∈S)
    (hP : P∈F) (hcP : c∉P) (hLP : ∀ x∈P,L≤x) :
    ((CrookedMembers F).card:ℝ)≤(PreparedCrooked F c L).card+(N:ℝ)+6*(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  have hh : ((CrookedMembers F).card:ℝ)≤(PreparedCrooked F c L).card+(N:ℝ)+(WitnessException (Ground N) c:ℝ) := by
    exact_mod_cast actual_prepared_crooked_count hF hroot hP hcP hLP
  have hW := DivisorMoment45.actual_exception_harmonic hcN
  linarith only [hh,hW]

theorem actual_prepared_member_witness {N : ℕ} {F : Finset (Finset ℤ)} {T S : Finset ℤ} {c L R : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ S∈F,¬IsAP S→c∈S)
    (hcL : c≤L) (hLR : L≤R) (hT : T∈F) (hcT : c∉T) (hTR : ∀ x∈T,x≤R)
    (hS : S∈PreparedCrooked F c L) :
    ∃ x p:ℤ,IntrinsicPair c S {x,p} ∧ x<p ∧ x≤R ∧ L<p ∧ x≠L ∧
      (c<x→x<L→R<p→S∩Finset.Icc x p={x,p} ∨ ¬IsAP (S∩Finset.Icc x p)) := by
  obtain ⟨hSH,hn⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSC,Q,hQ,hhigh⟩ := Finset.mem_filter.mp hSH
  obtain ⟨hSF,hbad⟩ := Finset.mem_filter.mp hSC
  have hcS := hroot S hSF hbad
  obtain ⟨t,ht⟩ := actual_avoider_meets_erase hF hSF hT hcS hcT
  obtain ⟨htS,htT⟩ := Finset.mem_inter.mp ht
  obtain ⟨htc,htS⟩ := Finset.mem_erase.mp htS
  have hreach := actual_witness_high_reaches_low hcS htS htc (hcL.trans hLR) (hTR t htT) hLR hQ hhigh
  exact actual_ordered_preferred_witness hLR hreach (fun W hw hLW=>hn ⟨W,hw,hLW⟩)

theorem actual_prepared_witness_choices {N : ℕ} {F : Finset (Finset ℤ)} {T : Finset ℤ} {c L R : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ S∈F,¬IsAP S→c∈S)
    (hcL : c≤L) (hLR : L≤R) (hT : T∈F) (hcT : c∉T) (hTR : ∀ x∈T,x≤R) :
    ∃ x p:Finset ℤ→ℤ,∀ S∈PreparedCrooked F c L,
      IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ x S≤R ∧ L<p S ∧ x S≠L ∧
        (c<x S→x S<L→R<p S→S∩Finset.Icc (x S) (p S)={x S,p S} ∨
          ¬IsAP (S∩Finset.Icc (x S) (p S))) := by
  have hex : ∀ S:Finset ℤ,∃ x p:ℤ,S∈PreparedCrooked F c L→
      IntrinsicPair c S {x,p} ∧ x<p ∧ x≤R ∧ L<p ∧ x≠L ∧
        (c<x→x<L→R<p→S∩Finset.Icc x p={x,p} ∨ ¬IsAP (S∩Finset.Icc x p)) := by
    intro S
    by_cases hS : S∈PreparedCrooked F c L
    · obtain ⟨x,p,hh⟩ := actual_prepared_member_witness hF hroot hcL hLR hT hcT hTR hS
      exact ⟨x,p,fun _=>hh⟩
    · exact ⟨0,0,fun hh=>False.elim (hS hh)⟩
  choose x p hx using hex
  exact ⟨x,p,hx⟩

theorem actual_original_prepared_crooked28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃ H : Finset (Finset ℤ),(H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
      (Deleted N 28 H).card=(Deleted N 28 F).card ∧
      (Retained N 28 H).card=(Retained N 28 F).card ∧
      ∃ c∈Ground N,∃ L R:ℕ,c<(L:ℤ) ∧ L≤R ∧ R≤N ∧
        (∀ S∈Retained N 28 H,¬IsAP S→c∈S) ∧
        (∀ S∈Avoiders (Retained N 28 H) c,IsAP S) ∧
        (∃ P∈Avoiders (Retained N 28 H) c,∀ z∈P,(L:ℤ)≤z) ∧
        (∃ T∈Avoiders (Retained N 28 H) c,∀ z∈T,z≤(R:ℤ)) ∧
        (PreparedCrooked (Retained N 28 H) c L⊆CrookedMembers (Retained N 28 H)) ∧
        (CrookedMembers (Retained N 28 H)).card≤
          (PreparedCrooked (Retained N 28 H) c L).card+N+WitnessException (Ground N) c ∧
        ∃ x p:Finset ℤ→ℤ,∀ S∈PreparedCrooked (Retained N 28 H) c L,
          IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ x S≤(R:ℤ) ∧ (L:ℤ)<p S ∧ x S≠(L:ℤ) ∧
            (c<x S→x S<(L:ℤ)→(R:ℤ)<p S→S∩Finset.Icc (x S) (p S)={x S,p S} ∨
              ¬IsAP (S∩Finset.Icc (x S) (p S))) := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,hroot,hAP,L,R,hLc,hLR,hRN,hP,hT,_henv⟩ :=
    OneSided47.actual_original_outside_envelope28 hN hF hcounter
  obtain ⟨P,hP,hLP⟩ := hP
  obtain ⟨T,hT,hTR⟩ := hT
  obtain ⟨hPF,hcP⟩ := Finset.mem_filter.mp hP
  obtain ⟨hTF,hcT⟩ := Finset.mem_filter.mp hT
  have hlegal := actual_retained_legal (r:=28) hLH
  have hcount := actual_prepared_crooked_count hlegal hroot hPF hcP hLP
  have hLRZ : (L:ℤ)≤R := by exact_mod_cast hLR
  obtain ⟨x,p,hx⟩ := actual_prepared_witness_choices hlegal hroot hLc.le hLRZ hTF hcT hTR
  refine ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hAP,
    ⟨P,Finset.mem_filter.mpr ⟨hPF,hcP⟩,hLP⟩,⟨T,Finset.mem_filter.mpr ⟨hTF,hcT⟩,hTR⟩,?_,hcount,x,p,hx⟩
  exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

#print axioms consecutive_subset
#print axioms actual_consecutive_step
#print axioms actual_AP_union_consecutive
#print axioms cover_of_not_intrinsic
#print axioms cover_mono
#print axioms cover_union_consecutive
#print axioms actual_intrinsic_redirect_neighbor
#print axioms actual_root_neighbor_le
#print axioms actual_witness_high_reaches_low
#print axioms actual_pair_eq_of_card_two
#print axioms actual_preferred_witness
#print axioms actual_consecutive_across_cut
#print axioms actual_consecutive_crop_card
#print axioms actual_preferred_AP_crop_card
#print axioms actual_preferred_crop_dichotomy
#print axioms actual_ordered_preferred_witness
#print axioms actual_division_point_witness_card
#print axioms actual_no_high_witness_card
#print axioms actual_prepared_crooked_count
#print axioms actual_prepared_crooked_harmonic
#print axioms actual_prepared_member_witness
#print axioms actual_prepared_witness_choices
#print axioms actual_original_prepared_crooked28
end
end JSP233.PreparedWitness48
