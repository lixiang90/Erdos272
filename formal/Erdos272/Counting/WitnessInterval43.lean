module

public import Erdos272.Retention.LongTerminal35

@[expose] public section

/-! Actual intrinsic witnesses and interval endpoints share one finite pool.
All resources below belong to the same legal family. -/
namespace JSP233.WitnessInterval43
open StarCompletion PrivatePairExistence LongTerminal35
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

def CrossPairs (L R : Finset ℤ) : Finset (Finset ℤ) :=
  (L.product R).image (fun p => {p.1,p.2})

def MeetingOutsidePairs (U B P : Finset ℤ) : Finset (Finset ℤ) :=
  (U.powersetCard 2).filter (fun Q => ¬Disjoint Q P ∧ ¬Q⊆B)

def IntervalPool (Ω : Finset ℤ) (c u v : ℤ) (P : Finset ℤ) : Finset (Finset ℤ) :=
  CrossPairs (Finset.Ico u c) (Finset.Ioc c v) ∪
    MeetingOutsidePairs (Ω.erase c) ((Finset.Icc u v).erase c) P

def StraddledIntervals (F : Finset (Finset ℤ)) (c : ℤ) : Finset (Finset ℤ) :=
  F.filter (fun S => ∃ a b : ℤ, a<c ∧ c<b ∧ S=Finset.Icc a b)

def RootCrooked (F : Finset (Finset ℤ)) (c : ℤ) : Finset (Finset ℤ) :=
  F.filter (fun S => c∈S ∧ ¬IsAP S)

def MeetingCrooked (F : Finset (Finset ℤ)) (c : ℤ) (P : Finset ℤ) : Finset (Finset ℤ) :=
  F.filter (fun S => c∈S ∧ ¬IsAP S ∧ ∃ Q, IntrinsicPair c S Q ∧ ¬Disjoint Q P)

def SupportedEnvelope (F : Finset (Finset ℤ)) (c u v : ℤ) : Prop :=
  u≤c ∧ c≤v ∧
    (u=c ∨ ∃ T∈F,IsAP T ∧ Finset.Icc u c⊆T) ∧
    (v=c ∨ ∃ T∈F,IsAP T ∧ Finset.Icc c v⊆T)

theorem integer_interval_isAP (a b : ℤ) (hab : a≤b) : IsAP (Finset.Icc a b) := by
  refine ⟨1,a,by omega,a,b,?_,Finset.mem_Icc.mpr ⟨le_rfl,hab⟩⟩
  intro x
  simp

theorem actual_intrinsic_pair_exists {S : Finset ℤ} {c : ℤ}
    (hc : c∈S) (hbad : ¬IsAP S) : ∃ Q, IntrinsicPair c S Q := by
  obtain ⟨u,hu,v,hv,huc,hvc,huv,⟨x,hx,hxn⟩,_⟩ :=
    missing_completion_at_root_exists hc hbad
  refine ⟨{u,v},by simp [huv],by simp [Ne.symm huc,Ne.symm hvc],?_,?_⟩
  · exact Finset.insert_subset_iff.mpr ⟨hu,Finset.singleton_subset_iff.mpr hv⟩
  · rintro ⟨T,hAP,hQT,hTS⟩
    apply hxn
    apply hTS
    exact completionAt_least hAP (hQT (by simp)) (hQT (by simp)) (hQT (by simp)) hx

theorem actual_intrinsic_member_eq {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {c : ℤ} {S T Q : Finset ℤ} (hF : Legal Ω F) (hS : S∈F) (hT : T∈F)
    (hcS : c∈S) (hcT : c∈T) (hQ : IntrinsicPair c S Q) (hQT : Q⊆T) : S=T := by
  by_contra hne
  apply hQ.2.2.2
  refine ⟨S∩T,hF.2 S hS T hT hne,?_,Finset.inter_subset_left⟩
  exact Finset.insert_subset_iff.mpr ⟨Finset.mem_inter.mpr ⟨hcS,hcT⟩,
    fun x hx => Finset.mem_inter.mpr ⟨hQ.2.2.1 hx,hQT hx⟩⟩

theorem witness_pair_not_subset_AP_member {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {c : ℤ} {S T Q : Finset ℤ} (hF : Legal Ω F) (hS : S∈F) (hT : T∈F)
    (hcS : c∈S) (hcT : c∈T) (hbad : ¬IsAP S) (hAP : IsAP T)
    (hQ : IntrinsicPair c S Q) : ¬Q⊆T := by
  intro hQT
  have he := actual_intrinsic_member_eq hF hS hT hcS hcT hQ hQT
  exact hbad (he ▸ hAP)

theorem cross_pairs_card_le (L R : Finset ℤ) :
    (CrossPairs L R).card≤L.card*R.card := by
  exact (Finset.card_image_le).trans_eq (Finset.card_product L R)

theorem actual_cross_pairs_card (u c v : ℤ) :
    (CrossPairs (Finset.Ico u c) (Finset.Ioc c v)).card=
      (Finset.Ico u c).card*(Finset.Ioc c v).card := by
  have hi : Set.InjOn (fun p:ℤ×ℤ => ({p.1,p.2}:Finset ℤ))
      (↑((Finset.Ico u c).product (Finset.Ioc c v)) : Set (ℤ×ℤ)) := by
    intro p hp q hq he
    obtain ⟨hpl,hpr⟩ := Finset.mem_product.mp hp
    obtain ⟨hql,hqr⟩ := Finset.mem_product.mp hq
    have hh := ordered_pair_injective
      (lt_trans (Finset.mem_Ico.mp hpl).2 (Finset.mem_Ioc.mp hpr).1)
      (lt_trans (Finset.mem_Ico.mp hql).2 (Finset.mem_Ioc.mp hqr).1) he
    exact Prod.ext hh.1 hh.2
  exact (Finset.card_image_of_injOn hi).trans (Finset.card_product _ _)

theorem actual_pool_parts_disjoint (Ω P : Finset ℤ) (c u v : ℤ) :
    Disjoint (CrossPairs (Finset.Ico u c) (Finset.Ioc c v))
      (MeetingOutsidePairs (Ω.erase c) ((Finset.Icc u v).erase c) P) := by
  apply Finset.disjoint_left.mpr
  intro Q hC hO
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨hpl,hpr⟩ := Finset.mem_product.mp hp
  have hl := Finset.mem_Ico.mp hpl
  have hr := Finset.mem_Ioc.mp hpr
  apply (Finset.mem_filter.mp hO).2.2
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl <;> exact Finset.mem_erase.mpr
    ⟨by omega,Finset.mem_Icc.mpr (by omega)⟩

theorem actual_interval_pool_card (Ω P : Finset ℤ) (c u v : ℤ) :
    (IntervalPool Ω c u v P).card=
      (Finset.Ico u c).card*(Finset.Ioc c v).card+
      (MeetingOutsidePairs (Ω.erase c) ((Finset.Icc u v).erase c) P).card := by
  rw [IntervalPool,Finset.card_union_of_disjoint (actual_pool_parts_disjoint Ω P c u v),
    actual_cross_pairs_card]

theorem root_pair_in_cross_of_inner {c u v : ℤ} {Q : Finset ℤ}
    (hcard : Q.card=2) (hc : c∉Q) (hinner : Q⊆Finset.Icc u v)
    (hleft : ¬Q⊆Finset.Icc u c) (hright : ¬Q⊆Finset.Icc c v) :
    Q∈CrossPairs (Finset.Ico u c) (Finset.Ioc c v) := by
  obtain ⟨x,y,_hxy,rfl⟩ := Finset.card_eq_two.mp hcard
  have hx := Finset.mem_Icc.mp (hinner (by simp : x∈({x,y}:Finset ℤ)))
  have hy := Finset.mem_Icc.mp (hinner (by simp : y∈({x,y}:Finset ℤ)))
  have hxc : x≠c := by intro he; apply hc; simp [he]
  have hyc : y≠c := by intro he; apply hc; simp [he]
  by_cases hxl : x<c
  · have hcy : c<y := by
      by_contra hn
      apply hleft
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl <;> exact Finset.mem_Icc.mpr (by omega)
    exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr
      ⟨Finset.mem_Ico.mpr ⟨hx.1,hxl⟩,Finset.mem_Ioc.mpr ⟨hcy,hy.2⟩⟩,rfl⟩
  · have hyl : y<c := by
      by_contra hn
      apply hright
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl <;> exact Finset.mem_Icc.mpr (by omega)
    exact Finset.mem_image.mpr ⟨(y,x),Finset.mem_product.mpr
      ⟨Finset.mem_Ico.mpr ⟨hy.1,hyl⟩,Finset.mem_Ioc.mpr ⟨by omega,hx.2⟩⟩,
      by simp only [Finset.pair_comm]⟩

theorem crooked_witness_in_interval_pool {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {c u v : ℤ} {S Q P : Finset ℤ} (hF : Legal Ω F) (hS : S∈F)
    (huc : u≤c) (hcv : c≤v) (hcS : c∈S) (hbad : ¬IsAP S)
    (hleft : u=c ∨ ∃ T∈F, IsAP T ∧ Finset.Icc u c⊆T)
    (hright : v=c ∨ ∃ T∈F, IsAP T ∧ Finset.Icc c v⊆T)
    (hQ : IntrinsicPair c S Q) (hmet : ¬Disjoint Q P) :
    Q∈IntervalPool Ω c u v P := by
  have hnl : ¬Q⊆Finset.Icc u c := by
    intro hsub
    rcases hleft with he|⟨T,hT,hAP,hcover⟩
    · have hh := Finset.card_le_card hsub
      simp only [he,Finset.Icc_self,Finset.card_singleton,hQ.1] at hh
      omega
    · exact witness_pair_not_subset_AP_member hF hS hT hcS
        (hcover (Finset.mem_Icc.mpr ⟨huc,le_rfl⟩)) hbad hAP hQ (hsub.trans hcover)
  have hnr : ¬Q⊆Finset.Icc c v := by
    intro hsub
    rcases hright with he|⟨T,hT,hAP,hcover⟩
    · have hh := Finset.card_le_card hsub
      simp only [he,Finset.Icc_self,Finset.card_singleton,hQ.1] at hh
      omega
    · exact witness_pair_not_subset_AP_member hF hS hT hcS
        (hcover (Finset.mem_Icc.mpr ⟨le_rfl,hcv⟩)) hbad hAP hQ (hsub.trans hcover)
  by_cases hin : Q⊆Finset.Icc u v
  · exact Finset.mem_union_left _ (root_pair_in_cross_of_inner hQ.1 hQ.2.1 hin hnl hnr)
  · apply Finset.mem_union_right
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_,hQ.1⟩,hmet,?_⟩
    · intro x hx
      exact Finset.mem_erase.mpr ⟨by intro he; exact hQ.2.1 (he ▸ hx),
        hF.1 S hS (hQ.2.2.1 hx)⟩
    · exact fun hh => hin (hh.trans (Finset.erase_subset _ _))

theorem private_pairs_and_intervals_card_le {Ω : Finset ℤ} {F C E : Finset (Finset ℤ)}
    {c : ℤ} {Pool : Finset (Finset ℤ)} (hF : Legal Ω F)
    (hCF : C⊆F) (hEF : E⊆F) (hc : ∀ S∈C,c∈S) (hbad : ∀ S∈C,¬IsAP S)
    (hW : ∀ S∈C,∃ Q,IntrinsicPair c S Q ∧ Q∈Pool)
    (hE : ∀ S∈E,∃ a b : ℤ,a<c ∧ c<b ∧ S=Finset.Icc a b ∧ ({a,b}:Finset ℤ)∈Pool) :
    C.card+E.card≤Pool.card := by
  let X := {S // S∈C}
  let Y := {S // S∈E}
  have hparamC : ∀ S:X,∃ Q,IntrinsicPair c S.val Q ∧ Q∈Pool := fun S => hW S.val S.property
  choose Q hQ hQP using hparamC
  have hparamE : ∀ T:Y,∃ a b:ℤ,a<c ∧ c<b ∧ T.val=Finset.Icc a b ∧ ({a,b}:Finset ℤ)∈Pool :=
    fun T => hE T.val T.property
  choose a b hac hcb hrep hEP using hparamE
  let e : Y→Finset ℤ := fun T => {a T,b T}
  have hQi : Function.Injective Q := by
    intro S T he
    apply Subtype.ext
    exact actual_intrinsic_member_eq hF (hCF S.property) (hCF T.property)
      (hc S.val S.property) (hc T.val T.property) (hQ S)
      (by rw [he]; exact (hQ T).2.2.1)
  have hei : Function.Injective e := by
    intro S T he
    have hh := ordered_pair_injective (lt_trans (hac S) (hcb S)) (lt_trans (hac T) (hcb T)) he
    apply Subtype.ext
    rw [hrep S,hrep T,hh.1,hh.2]
  have hd : Disjoint ((Finset.univ:Finset X).image Q) ((Finset.univ:Finset Y).image e) := by
    apply Finset.disjoint_left.mpr
    intro W hWC hWE
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hWC
    obtain ⟨T,_,he⟩ := Finset.mem_image.mp hWE
    have hab := le_of_lt (lt_trans (hac T) (hcb T))
    have hAP : IsAP T.val := by rw [hrep T]; exact integer_interval_isAP _ _ hab
    have hcT : c∈T.val := by rw [hrep T]; exact Finset.mem_Icc.mpr ⟨(hac T).le,(hcb T).le⟩
    apply witness_pair_not_subset_AP_member hF (hCF S.property) (hEF T.property)
      (hc S.val S.property) hcT (hbad S.val S.property) hAP (hQ S)
    rw [←he,hrep T]
    intro x hx
    simp only [e,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact Finset.mem_Icc.mpr ⟨le_rfl,hab⟩
    · exact Finset.mem_Icc.mpr ⟨hab,le_rfl⟩
  have hs : ((Finset.univ:Finset X).image Q)∪((Finset.univ:Finset Y).image e)⊆Pool := by
    intro W hW
    rcases Finset.mem_union.mp hW with hC|hE
    · obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hC
      exact hQP S
    · obtain ⟨T,_,rfl⟩ := Finset.mem_image.mp hE
      exact hEP T
  have hh := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ hQi,
    Finset.card_image_of_injective _ hei] at hh
  simpa only [Finset.card_univ,X,Y,Fintype.card_coe] using hh

theorem rooted_interval_envelope {c : ℤ} {E : Finset (Finset ℤ)}
    (hc : ∀ S∈E,c∈S) (hi : ∀ S∈E,∃ a b:ℤ,S=Finset.Icc a b) :
    ∃ u v : ℤ, u≤c ∧ c≤v ∧
      (u=c ∨ ∃ T∈E,IsAP T ∧ Finset.Icc u c⊆T) ∧
      (v=c ∨ ∃ T∈E,IsAP T ∧ Finset.Icc c v⊆T) ∧
      ∀ S∈E,∃ a b:ℤ,u≤a ∧ a≤c ∧ c≤b ∧ b≤v ∧ S=Finset.Icc a b := by
  by_cases hn : E.Nonempty
  · let X := {S // S∈E}
    have hp : ∀ S:X,∃ a b:ℤ,S.val=Finset.Icc a b := fun S => hi S.val S.property
    choose a b hr using hp
    have hab : ∀ S:X,a S≤c ∧ c≤b S := fun S => Finset.mem_Icc.mp (hr S ▸ hc S.val S.property)
    have hX : (Finset.univ:Finset X).Nonempty := by
      obtain ⟨S,hS⟩ := hn
      exact ⟨⟨S,hS⟩,Finset.mem_univ _⟩
    obtain ⟨L,_,hmin⟩ := Finset.exists_min_image Finset.univ a hX
    obtain ⟨R,_,hmax⟩ := Finset.exists_max_image Finset.univ b hX
    refine ⟨a L,b R,(hab L).1,(hab R).2,?_,?_,?_⟩
    · refine Or.inr ⟨L.val,L.property,?_,?_⟩
      · rw [hr L]; exact integer_interval_isAP _ _ ((hab L).1.trans (hab L).2)
      · intro x hx
        rw [hr L]
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1,(Finset.mem_Icc.mp hx).2.trans (hab L).2⟩
    · refine Or.inr ⟨R.val,R.property,?_,?_⟩
      · rw [hr R]; exact integer_interval_isAP _ _ ((hab R).1.trans (hab R).2)
      · intro x hx
        rw [hr R]
        exact Finset.mem_Icc.mpr ⟨(hab R).1.trans (Finset.mem_Icc.mp hx).1,(Finset.mem_Icc.mp hx).2⟩
    · intro S hS
      let T:X := ⟨S,hS⟩
      exact ⟨a T,b T,hmin T (Finset.mem_univ _),(hab T).1,(hab T).2,hmax T (Finset.mem_univ _),hr T⟩
  · refine ⟨c,c,le_rfl,le_rfl,Or.inl rfl,Or.inl rfl,?_⟩
    intro S hS
    exact False.elim (hn ⟨S,hS⟩)

theorem actual_meeting_crooked_interval_budget {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hF : Legal Ω F) :
    ∃ u v : ℤ,SupportedEnvelope F c u v ∧
      (MeetingCrooked F c P).card+(StraddledIntervals F c).card≤(IntervalPool Ω c u v P).card := by
  let C := MeetingCrooked F c P
  let E := StraddledIntervals F c
  have hEF : E⊆F := fun S hS => (Finset.mem_filter.mp hS).1
  have hi : ∀ S∈E,∃ a b:ℤ,a<c ∧ c<b ∧ S=Finset.Icc a b :=
    fun S hS => (Finset.mem_filter.mp hS).2
  have hcE : ∀ S∈E,c∈S := by
    intro S hS
    obtain ⟨a,b,ha,hb,he⟩ := hi S hS
    rw [he]
    exact Finset.mem_Icc.mpr ⟨ha.le,hb.le⟩
  obtain ⟨u,v,huc,hcv,hl,hr,hall⟩ := rooted_interval_envelope hcE (fun S hS => by
    obtain ⟨a,b,_,_,he⟩ := hi S hS
    exact ⟨a,b,he⟩)
  have hlF : u=c ∨ ∃ T∈F,IsAP T ∧ Finset.Icc u c⊆T := by
    rcases hl with he|⟨T,hT,hAP,hs⟩
    · exact Or.inl he
    · exact Or.inr ⟨T,hEF hT,hAP,hs⟩
  have hrF : v=c ∨ ∃ T∈F,IsAP T ∧ Finset.Icc c v⊆T := by
    rcases hr with he|⟨T,hT,hAP,hs⟩
    · exact Or.inl he
    · exact Or.inr ⟨T,hEF hT,hAP,hs⟩
  refine ⟨u,v,⟨huc,hcv,hlF,hrF⟩,?_⟩
  apply private_pairs_and_intervals_card_le hF (fun S hS => (Finset.mem_filter.mp hS).1) hEF
    (fun S hS => (Finset.mem_filter.mp hS).2.1) (fun S hS => (Finset.mem_filter.mp hS).2.2.1)
  · intro S hS
    obtain ⟨hSF,hcS,hbad,Q,hQ,hmet⟩ := Finset.mem_filter.mp hS
    exact ⟨Q,hQ,crooked_witness_in_interval_pool hF hSF huc hcv hcS hbad hlF hrF hQ hmet⟩
  · intro S hS
    obtain ⟨a,b,hua,hac,hcb,hbv,he⟩ := hall S hS
    have hcS := hcE S hS
    obtain ⟨a',b',ha',hb',he'⟩ := hi S hS
    have hae : a=a' := by
      have h1 : a∈Finset.Icc a' b' := by rw [←he',he]; exact Finset.mem_Icc.mpr ⟨le_rfl,hac.trans hcb⟩
      have h2 : a'∈Finset.Icc a b := by rw [←he,he']; exact Finset.mem_Icc.mpr ⟨le_rfl,ha'.le.trans hb'.le⟩
      have := Finset.mem_Icc.mp h1
      have := Finset.mem_Icc.mp h2
      omega
    have hbe : b=b' := by
      have h1 : b∈Finset.Icc a' b' := by rw [←he',he]; exact Finset.mem_Icc.mpr ⟨hac.trans hcb,le_rfl⟩
      have h2 : b'∈Finset.Icc a b := by rw [←he,he']; exact Finset.mem_Icc.mpr ⟨ha'.le.trans hb'.le,le_rfl⟩
      have := Finset.mem_Icc.mp h1
      have := Finset.mem_Icc.mp h2
      omega
    have hac' : a<c := hae ▸ ha'
    have hcb' : c<b := hbe ▸ hb'
    refine ⟨a,b,hac',hcb',he,Finset.mem_union_left _ ?_⟩
    exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr
      ⟨Finset.mem_Ico.mpr ⟨hua,hac'⟩,Finset.mem_Ioc.mpr ⟨hcb',hbv⟩⟩,rfl⟩

theorem actual_all_meeting_eq_root_crooked {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (c : ℤ) (hF : Legal Ω F) : MeetingCrooked F c (Ω.erase c)=RootCrooked F c := by
  ext S
  constructor
  · intro hS
    obtain ⟨hSF,hc,hbad,_⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨hSF,hc,hbad⟩
  · intro hS
    obtain ⟨hSF,hc,hbad⟩ := Finset.mem_filter.mp hS
    obtain ⟨Q,hQ⟩ := actual_intrinsic_pair_exists hc hbad
    refine Finset.mem_filter.mpr ⟨hSF,hc,hbad,Q,hQ,?_⟩
    intro hd
    have hn : Q.Nonempty := Finset.card_pos.mp (by rw [hQ.1]; omega)
    obtain ⟨x,hx⟩ := hn
    exact Finset.disjoint_left.mp hd hx (Finset.mem_erase.mpr
      ⟨by intro he; exact hQ.2.1 (he ▸ hx),hF.1 S hSF (hQ.2.2.1 hx)⟩)

theorem actual_all_crooked_interval_budget {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (c : ℤ) (hF : Legal Ω F) :
    ∃ u v : ℤ,SupportedEnvelope F c u v ∧
      (RootCrooked F c).card+(StraddledIntervals F c).card≤
        (IntervalPool Ω c u v (Ω.erase c)).card := by
  simpa only [actual_all_meeting_eq_root_crooked c hF] using
    actual_meeting_crooked_interval_budget c (Ω.erase c) hF

theorem actual_ground_meeting_budget {N : ℕ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hc : c∈Ground N) (hF : Legal (Ground N) F) :
    ∃ u v : ℤ,1≤u ∧ u≤c ∧ c≤v ∧ v≤N ∧
      (MeetingCrooked F c P).card+(StraddledIntervals F c).card≤
        (IntervalPool (Ground N) c u v P).card := by
  obtain ⟨u,v,⟨huc,hcv,hl,hr⟩,hb⟩ := actual_meeting_crooked_interval_budget c P hF
  have hu : u∈Ground N := by
    rcases hl with he|⟨T,hT,_hAP,hs⟩
    · exact he ▸ hc
    · exact hF.1 T hT (hs (Finset.mem_Icc.mpr ⟨le_rfl,huc⟩))
  have hv : v∈Ground N := by
    rcases hr with he|⟨T,hT,_hAP,hs⟩
    · exact he ▸ hc
    · exact hF.1 T hT (hs (Finset.mem_Icc.mpr ⟨hcv,le_rfl⟩))
  exact ⟨u,v,((mem_ground N u).mp hu).1,huc,hcv,((mem_ground N v).mp hv).2,hb⟩

theorem actual_ground_all_crooked_budget {N : ℕ} {F : Finset (Finset ℤ)}
    (c : ℤ) (hc : c∈Ground N) (hF : Legal (Ground N) F) :
    ∃ u v : ℤ,1≤u ∧ u≤c ∧ c≤v ∧ v≤N ∧
      (RootCrooked F c).card+(StraddledIntervals F c).card≤
        (IntervalPool (Ground N) c u v ((Ground N).erase c)).card := by
  simpa only [actual_all_meeting_eq_root_crooked c hF] using
    actual_ground_meeting_budget c ((Ground N).erase c) hc hF

theorem actual_common_crooked_ground_budget {N : ℕ} {F : Finset (Finset ℤ)}
    (c : ℤ) (hc : c∈Ground N) (hF : Legal (Ground N) F)
    (hroot : ∀ S∈F,¬IsAP S → c∈S) :
    ∃ u v : ℤ,1≤u ∧ u≤c ∧ c≤v ∧ v≤N ∧
      (CrookedMembers F).card+(StraddledIntervals F c).card≤
        (IntervalPool (Ground N) c u v ((Ground N).erase c)).card := by
  have he : RootCrooked F c=CrookedMembers F := by
    ext S
    simp only [RootCrooked,CrookedMembers,Finset.mem_filter]
    constructor
    · rintro ⟨hSF,_hcS,hbad⟩
      exact ⟨hSF,hbad⟩
    · rintro ⟨hSF,hbad⟩
      exact ⟨hSF,hroot S hSF hbad,hbad⟩
  simpa only [he] using actual_ground_all_crooked_budget c hc hF

#print axioms actual_intrinsic_pair_exists
#print axioms integer_interval_isAP
#print axioms actual_intrinsic_member_eq
#print axioms witness_pair_not_subset_AP_member
#print axioms cross_pairs_card_le
#print axioms actual_cross_pairs_card
#print axioms actual_pool_parts_disjoint
#print axioms actual_interval_pool_card
#print axioms root_pair_in_cross_of_inner
#print axioms crooked_witness_in_interval_pool
#print axioms private_pairs_and_intervals_card_le
#print axioms rooted_interval_envelope
#print axioms actual_meeting_crooked_interval_budget
#print axioms actual_all_meeting_eq_root_crooked
#print axioms actual_all_crooked_interval_budget
#print axioms actual_ground_meeting_budget
#print axioms actual_ground_all_crooked_budget
#print axioms actual_common_crooked_ground_budget
end
end JSP233.WitnessInterval43
