module

public import Erdos272.Core.CoreAP34

@[expose] public section

/-! Actual interval reservations and joint root resources.  The geometric
crooked witness premise, when present, is explicit; no cardinality bound
for the retained family is assumed. -/
namespace JSP233.LongTerminal35
open StarCompletion PrivatePairExistence StarResources30 StepHall33 CoreAP34
open scoped Classical BigOperators
noncomputable section

def Interval (p : ℕ×ℕ) : Finset ℤ := Finset.Icc (p.1:ℤ) (p.2:ℤ)
def Intervals (I : Finset (ℕ×ℕ)) : Finset (Finset ℤ) := I.image Interval
def ValidIntervals (N c L R : ℕ) (I : Finset (ℕ×ℕ)) : Prop :=
  ∀ p∈I, c<p.1 ∧ p.1≤L ∧ R≤p.2 ∧ p.2≤N
def Boundary (c N : ℕ) (I : Finset (ℕ×ℕ)) : Finset (ℕ×ℕ) :=
  I.filter (fun p => p.1=c+1 ∨ p.2=N)
def Interior (c N : ℕ) (I : Finset (ℕ×ℕ)) : Finset (ℕ×ℕ) :=
  I.filter (fun p => ¬(p.1=c+1 ∨ p.2=N))
def ReservedPair (p : ℕ×ℕ) : Finset ℤ := {((p.1:ℤ)-1),(p.2:ℤ)+1}
def Reserved (c N : ℕ) (I : Finset (ℕ×ℕ)) : Finset (Finset ℤ) :=
  (Interior c N I).image ReservedPair
def BoundaryCode (c N : ℕ) (p : ℕ×ℕ) : ℕ :=
  if p.1=c+1 then if p.2=N then c else p.2+1 else p.1-1
def CenterPool (c N : ℕ) (I : Finset (ℕ×ℕ)) : Finset ℤ :=
  (Finset.Icc ((c:ℤ)+1) (N:ℤ)).filter (fun x => ∀ p∈I, x∈Interval p)

theorem ordered_pair_injective {a b u v : ℤ} (hab : a<b) (huv : u<v)
    (he : ({a,b}:Finset ℤ)={u,v}) : a=u ∧ b=v := by
  have ha : a=u ∨ a=v := by simpa only [Finset.mem_insert,Finset.mem_singleton]
    using (show a∈({u,v}:Finset ℤ) by rw [←he]; simp)
  have hb : b=u ∨ b=v := by simpa only [Finset.mem_insert,Finset.mem_singleton]
    using (show b∈({u,v}:Finset ℤ) by rw [←he]; simp)
  rcases ha with ha|ha <;> rcases hb with hb|hb <;> omega

theorem interval_injective_on (N c L R : ℕ) (I : Finset (ℕ×ℕ))
    (hLR : L≤R) (hv : ValidIntervals N c L R I) : Set.InjOn Interval I := by
  intro p hp q hq he
  obtain ⟨_,hpL,hRp,_⟩ := hv p hp
  obtain ⟨_,hqL,hRq,_⟩ := hv q hq
  have hp12 : (p.1:ℤ)≤p.2 := by exact_mod_cast (show p.1≤p.2 by omega)
  have hq12 : (q.1:ℤ)≤q.2 := by exact_mod_cast (show q.1≤q.2 by omega)
  have hpl : (p.1:ℤ)∈Interval q := he ▸ Finset.mem_Icc.mpr ⟨le_rfl,hp12⟩
  have hpr : (p.2:ℤ)∈Interval q := he ▸ Finset.mem_Icc.mpr ⟨hp12,le_rfl⟩
  have hql : (q.1:ℤ)∈Interval p := he.symm ▸ Finset.mem_Icc.mpr ⟨le_rfl,hq12⟩
  have hqr : (q.2:ℤ)∈Interval p := he.symm ▸ Finset.mem_Icc.mpr ⟨hq12,le_rfl⟩
  simp only [Interval,Finset.mem_Icc] at hpl hpr hql hqr
  apply Prod.ext <;> omega

theorem intervals_card (N c L R : ℕ) (I : Finset (ℕ×ℕ))
    (hLR : L≤R) (hv : ValidIntervals N c L R I) : (Intervals I).card=I.card := by
  exact Finset.card_image_of_injOn (interval_injective_on N c L R I hLR hv)

theorem reserved_injective_on (N c L R : ℕ) (I : Finset (ℕ×ℕ))
    (hLR : L≤R) (hv : ValidIntervals N c L R I) : Set.InjOn ReservedPair I := by
  intro p hp q hq he
  obtain ⟨_,hpL,hRp,_⟩ := hv p hp
  obtain ⟨_,hqL,hRq,_⟩ := hv q hq
  have hpp : (p.1:ℤ)-1<(p.2:ℤ)+1 := by exact_mod_cast (show (p.1:ℤ)-1<(p.2:ℤ)+1 by omega)
  have hqq : (q.1:ℤ)-1<(q.2:ℤ)+1 := by omega
  have hh := ordered_pair_injective hpp hqq he
  apply Prod.ext <;> omega

theorem reserved_card_partition (N c L R : ℕ) (I : Finset (ℕ×ℕ))
    (hLR : L≤R) (hv : ValidIntervals N c L R I) :
    (Reserved c N I).card+(Boundary c N I).card=I.card := by
  have hi : Interior c N I⊆I := Finset.filter_subset _ _
  have hc := Finset.card_image_of_injOn
    ((reserved_injective_on N c L R I hLR hv).mono hi)
  change (Reserved c N I).card=(Interior c N I).card at hc
  have hp := Finset.card_filter_add_card_filter_not (s:=I)
    (fun p => p.1=c+1 ∨ p.2=N)
  change (Boundary c N I).card+(Interior c N I).card=I.card at hp
  omega

theorem reserved_geometry (N c L R : ℕ) (I : Finset (ℕ×ℕ))
    (hc : 1≤c) (hLR : L≤R) (hv : ValidIntervals N c L R I)
    {Q : Finset ℤ} (hQ : Q∈Reserved c N I) :
    Q∈PairUniverse (c:ℤ) (Ground N) ∧ ExteriorPair (c:ℤ) (L:ℤ) (R:ℤ) Q := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨hpI,hpB⟩ := Finset.mem_filter.mp hp
  obtain ⟨hcp,hpL,hRp,hpN⟩ := hv p hpI
  have ha : c+1<p.1 := by omega
  have hb : p.2<N := by omega
  have hab : (p.1:ℤ)-1<(p.2:ℤ)+1 := by omega
  constructor
  · apply Finset.mem_powersetCard.mpr
    refine ⟨?_,by simp [ReservedPair,hab.ne]⟩
    intro x hx
    simp only [ReservedPair,Finset.mem_insert,Finset.mem_singleton] at hx
    apply Finset.mem_erase.mpr
    rcases hx with rfl|rfl
    · refine ⟨by omega,(mem_ground _ _).mpr ⟨by omega,by omega⟩⟩
    · refine ⟨by omega,(mem_ground _ _).mpr ⟨by omega,by omega⟩⟩
  · exact ⟨(p.1:ℤ)-1,(p.2:ℤ)+1,rfl,by omega,by omega,by omega⟩

theorem legal_root_interval_between (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hLR : L≤R) (hv : ValidIntervals N c L R I)
    (hlegal : Legal (Ground N) (H∪Intervals I)) (hroot : Rooted H (c:ℤ))
    {S : Finset ℤ} (hS : S∈H) {u v : ℤ} (huv : u<v)
    (hW : ({u,v}:Finset ℤ)∈Reserved c N I) : ∃ x∈S, u<x ∧ x<v := by
  obtain ⟨p,hp,hpair⟩ := Finset.mem_image.mp hW
  obtain ⟨hpI,_⟩ := Finset.mem_filter.mp hp
  obtain ⟨hcp,hpL,hRp,_⟩ := hv p hpI
  have hab : (p.1:ℤ)-1<(p.2:ℤ)+1 := by omega
  have he := ordered_pair_injective hab huv hpair
  have hcnot : (c:ℤ)∉Interval p := by simp only [Interval,Finset.mem_Icc]; omega
  have hne : S≠Interval p := by intro he; exact hcnot (he ▸ hroot S hS)
  have hinter := hlegal.2 S (Finset.mem_union_left _ hS) (Interval p)
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hpI,rfl⟩)) hne
  obtain ⟨x,hx⟩ := isAP_nonempty hinter
  obtain ⟨hxS,hxp⟩ := Finset.mem_inter.mp hx
  have hx := Finset.mem_Icc.mp hxp
  exact ⟨x,hxS,by omega,by omega⟩

theorem root_triple_erase_not_reserved (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hLR : L≤R)
    (hv : ValidIntervals N c L R I) (hlegal : Legal (Ground N) (H∪Intervals I))
    (hroot : Rooted H (c:ℤ)) {S : Finset ℤ} (hS : S∈H) :
    S.erase (c:ℤ)∉Reserved c N I := by
  intro hW
  obtain ⟨u,v,hrep,hcu,huL,hRv⟩ := (reserved_geometry N c L R I hc hLR hv hW).2
  have huv : u<v := by omega
  obtain ⟨x,hx,hux,hxv⟩ := legal_root_interval_between N c L R H I hLR hv hlegal hroot hS huv
    (by rw [←hrep]; exact hW)
  have hSS : S=insert (c:ℤ) {u,v} := by rw [←hrep,Finset.insert_erase (hroot S hS)]
  simp only [hSS,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx|hx|hx <;> omega

theorem boundary_code_bounds (N c L R : ℕ) (I : Finset (ℕ×ℕ))
    (_hLR : L≤R) (hv : ValidIntervals N c L R I) {p : ℕ×ℕ}
    (hp : p∈Boundary c N I) : c≤BoundaryCode c N p ∧ BoundaryCode c N p≤N ∧
      (BoundaryCode c N p:ℤ)∉Interval p := by
  obtain ⟨hpI,hpB⟩ := Finset.mem_filter.mp hp
  obtain ⟨hcp,hpL,hRp,hpN⟩ := hv p hpI
  unfold BoundaryCode
  split_ifs <;> simp only [Interval,Finset.mem_Icc] <;> omega

theorem boundary_code_injective (N c L R : ℕ) (I : Finset (ℕ×ℕ))
    (_hLR : L≤R) (hv : ValidIntervals N c L R I)
    (hmeet : ∀ p∈I, ∀ q∈I, ∃ x:ℤ, x∈Interval p ∧ x∈Interval q) :
    Set.InjOn (BoundaryCode c N) (Boundary c N I) := by
  intro p hp q hq he
  obtain ⟨hpI,hpB⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqI,hqB⟩ := Finset.mem_filter.mp hq
  obtain ⟨hcp,hpL,hRp,hpN⟩ := hv p hpI
  obtain ⟨hcq,hqL,hRq,hqN⟩ := hv q hqI
  obtain ⟨x,hxp,hxq⟩ := hmeet p hpI q hqI
  simp only [Interval,Finset.mem_Icc] at hxp hxq
  unfold BoundaryCode at he
  split_ifs at he <;> apply Prod.ext <;> omega

theorem legal_interval_meet (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hLR : L≤R) (hv : ValidIntervals N c L R I)
    (hlegal : Legal (Ground N) (H∪Intervals I)) :
    ∀ p∈I, ∀ q∈I, ∃ x:ℤ, x∈Interval p ∧ x∈Interval q := by
  intro p hp q hq
  by_cases he : Interval p=Interval q
  · obtain ⟨_,hpL,hRp,_⟩ := hv p hp
    have hx : (L:ℤ)∈Interval p := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    exact ⟨L,hx,he ▸ hx⟩
  · obtain ⟨x,hx⟩ := isAP_nonempty (hlegal.2 (Interval p)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)) (Interval q)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)) he)
    exact ⟨x,Finset.mem_inter.mp hx⟩

theorem actual_small_boundary_payment (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (_hc : 1≤c) (hLR : L≤R)
    (hv : ValidIntervals N c L R I) (hne : I.Nonempty)
    (hlegal : Legal (Ground N) (H∪Intervals I)) (hroot : Rooted H (c:ℤ)) :
    (APSmall H).card+(Boundary c N I).card≤N-c+1 := by
  have hH : Legal (Ground N) H := ⟨fun S hS => hlegal.1 S (Finset.mem_union_left _ hS),
    fun S hS T hT he => hlegal.2 S (Finset.mem_union_left _ hS) T (Finset.mem_union_left _ hT) he⟩
  let K := CenterPool c N I
  let C := (Boundary c N I).image (fun p => (BoundaryCode c N p:ℤ))
  have hsmall : APSmall H⊆PairStar K (c:ℤ) := by
    intro S hS
    obtain ⟨x,hxG,hSx⟩ := Finset.mem_image.mp (apSmall_subset_pairStar (c:ℤ) (Ground N) H hH hroot hS)
    have hSF := (Finset.mem_filter.mp hS).1
    have hxI : ∀ p∈I, x∈Interval p := by
      intro p hp
      obtain ⟨hcp,_,_,_⟩ := hv p hp
      have hcnot : (c:ℤ)∉Interval p := by simp only [Interval,Finset.mem_Icc]; omega
      have hneS : S≠Interval p := by intro he; exact hcnot (he ▸ hroot S hSF)
      obtain ⟨y,hy⟩ := isAP_nonempty (hlegal.2 S (Finset.mem_union_left _ hSF) (Interval p)
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)) hneS)
      obtain ⟨hyS,hyp⟩ := Finset.mem_inter.mp hy
      rw [←hSx] at hyS
      simp only [Finset.mem_insert,Finset.mem_singleton] at hyS
      rcases hyS with rfl|rfl
      · exact False.elim (hcnot hyp)
      · exact hyp
    have hxK : x∈K := by
      obtain ⟨p,hp⟩ := hne
      obtain ⟨hcp,_,_,_⟩ := hv p hp
      have hxp := Finset.mem_Icc.mp (hxI p hp)
      have hxN := (mem_ground N x).mp hxG
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hxN.2⟩,hxI⟩
    exact Finset.mem_image.mpr ⟨x,hxK,hSx⟩
  have hsc := (Finset.card_le_card hsmall).trans_eq (pairStar_card K (c:ℤ))
  have hbc : C.card=(Boundary c N I).card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq he
    have hcode : BoundaryCode c N p=BoundaryCode c N q := by
      change (BoundaryCode c N p:ℤ)=(BoundaryCode c N q:ℤ) at he
      exact_mod_cast he
    exact boundary_code_injective N c L R I hLR hv (legal_interval_meet N c L R H I hLR hv hlegal) hp hq hcode
  have hdis : Disjoint K C := by
    apply Finset.disjoint_left.mpr
    intro x hxK hxC
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hxC
    exact (boundary_code_bounds N c L R I hLR hv hp).2.2
      ((Finset.mem_filter.mp hxK).2 p (Finset.mem_filter.mp hp).1)
  have hsub : K∪C⊆Finset.Icc (c:ℤ) (N:ℤ) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1
      exact Finset.mem_Icc.mpr ⟨by omega,hh.2⟩
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hl,hr,_⟩ := boundary_code_bounds N c L R I hLR hv hp
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hl,by exact_mod_cast hr⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,hbc] at hcard
  have hcN : c≤N := by obtain ⟨p,hp⟩ := hne; obtain ⟨_,hpL,hRp,hpN⟩ := hv p hp; omega
  have hIcc : (Finset.Icc (c:ℤ) (N:ℤ)).card=N-c+1 := by
    simp only [Int.card_Icc]
    omega
  rw [hIcc] at hcard
  omega

def IntrinsicPair (c : ℤ) (S Q : Finset ℤ) : Prop :=
  Q.card=2 ∧ c∉Q ∧ Q⊆S ∧ ¬∃ T : Finset ℤ, IsAP T ∧ insert c Q⊆T ∧ T⊆S

def OutsideAvailable (c : ℤ) (Ω : Finset ℤ) (H W : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  AvailableBadPairsAt c Ω H \ W

def CrookedWitnesses (c : ℤ) (H W : Finset (Finset ℤ)) : Prop :=
  ∀ S∈H, ¬IsAP S → ∃ Q, IntrinsicPair c S Q ∧ Q∉W

theorem intrinsic_pair_private {Ω : Finset ℤ} {H : Finset (Finset ℤ)} {c : ℤ}
    (hlegal : Legal Ω H) (hroot : Rooted H c) {S Q : Finset ℤ}
    (hS : S∈H) (hQ : IntrinsicPair c S Q) :
    Q∈AvailableBadPairsAt c Ω H ∧ ∀ T∈H, T≠S → ¬Q⊆T := by
  obtain ⟨hcard,hcQ,hsub,hno⟩ := hQ
  have hp : ∀ T∈H, T≠S → ¬Q⊆T := by
    intro T hT he hQT
    apply hno
    refine ⟨S∩T,hlegal.2 S hS T hT he.symm,?_,Finset.inter_subset_left⟩
    exact Finset.insert_subset_iff.mpr ⟨Finset.mem_inter.mpr ⟨hroot S hS,hroot T hT⟩,
      fun x hx => Finset.mem_inter.mpr ⟨hsub hx,hQT hx⟩⟩
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hsub.trans (hlegal.1 S hS)),
    hcard,hcQ,?_,?_⟩,hp⟩
  · intro hAP
    exact hno ⟨insert c Q,hAP,Finset.Subset.refl _,Finset.insert_subset_iff.mpr ⟨hroot S hS,hsub⟩⟩
  · intro T hT hAP hQT
    by_cases he : T=S
    · subst T
      exact hno ⟨S,hAP,Finset.insert_subset_iff.mpr ⟨hroot S hS,hsub⟩,Finset.Subset.refl _⟩
    · exact hp T hT he hQT

theorem crooked_outside_available_card {Ω : Finset ℤ} {H W : Finset (Finset ℤ)} {c : ℤ}
    (hlegal : Legal Ω H) (hroot : Rooted H c) (hw : CrookedWitnesses c H W) :
    (CrookedMembers H).card≤(OutsideAvailable c Ω H W).card := by
  have hex : ∀ S : CrookedMembers H, ∃ Q : OutsideAvailable c Ω H W,
      Q.val⊆S.val ∧ ∀ T∈H, T≠S.val → ¬Q.val⊆T := by
    intro S
    obtain ⟨hSH,hbad⟩ := Finset.mem_filter.mp S.property
    obtain ⟨Q,hQ,hQW⟩ := hw S.val hSH hbad
    obtain ⟨ha,hp⟩ := intrinsic_pair_private hlegal hroot hSH hQ
    exact ⟨⟨Q,Finset.mem_sdiff.mpr ⟨ha,hQW⟩⟩,hQ.2.2.1,hp⟩
  choose f hf using hex
  apply Finset.card_le_card_of_injective (f:=f)
  intro S T he
  apply Subtype.ext
  by_contra hne
  have hnot := (hf S).2 T.val (Finset.mem_filter.mp T.property).1 (Ne.symm hne)
  apply hnot
  rw [show (f S).val=(f T).val from congrArg Subtype.val he]
  exact (hf T).1

theorem core_APLarge_subset_covered (N c L R : ℕ) (H : Finset (Finset ℤ)) :
    CoreAPPairs N c L R (APLarge H)⊆CoveredAPBadPairs (c:ℤ) (Ground N) H := by
  intro Q hQ
  obtain ⟨hc,_⟩ := Finset.mem_filter.mp hQ
  obtain ⟨hp,hcard,hroot,hbad,S,hS,hAP,hsub⟩ := Finset.mem_filter.mp hc
  exact Finset.mem_filter.mpr ⟨hp,hcard,hroot,hbad,S,(Finset.mem_filter.mp hS).1,hAP,hsub⟩

theorem actual_root_resources_with_reservation (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hLR : L≤R)
    (hv : ValidIntervals N c L R I) (hlegal : Legal (Ground N) (H∪Intervals I))
    (hroot : Rooted H (c:ℤ)) :
    (APTriples H).card+(CoreAPPairs N c L R (APLarge H)).card+
      (OutsideAvailable (c:ℤ) (Ground N) H (Reserved c N I)).card+(Reserved c N I).card≤
      (PairUniverse (c:ℤ) (Ground N)).card := by
  have hH : Legal (Ground N) H := ⟨fun S hS => hlegal.1 S (Finset.mem_union_left _ hS),
    fun S hS T hT he => hlegal.2 S (Finset.mem_union_left _ hS) T (Finset.mem_union_left _ hT) he⟩
  let T := TriplePairs (c:ℤ) H
  let P := CoreAPPairs N c L R (APLarge H)
  let A := OutsideAvailable (c:ℤ) (Ground N) H (Reserved c N I)
  let W := Reserved c N I
  let U := PairUniverse (c:ℤ) (Ground N)
  have hPC : P⊆CoveredAPBadPairs (c:ℤ) (Ground N) H := core_APLarge_subset_covered N c L R H
  have hAA : A⊆AvailableBadPairsAt (c:ℤ) (Ground N) H := Finset.sdiff_subset
  have hdTP : Disjoint T P := (triples_disjoint_covered (c:ℤ) (Ground N) H hH hroot).mono_right hPC
  have hdTA : Disjoint T A := (triples_disjoint_available (c:ℤ) (Ground N) H hH hroot).mono_right hAA
  have hdPA : Disjoint P A := (covered_disjoint_available (c:ℤ) (Ground N) H).mono hPC hAA
  have hdTW : Disjoint T W := by
    apply Finset.disjoint_left.mpr
    intro Q hT hW
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
    exact root_triple_erase_not_reserved N c L R H I hc hLR hv hlegal hroot
      (Finset.mem_filter.mp hS).1 hW
  have hdPW : Disjoint P W := by
    apply Finset.disjoint_left.mpr
    intro Q hP hW
    exact (Finset.mem_filter.mp hP).2 (reserved_geometry N c L R I hc hLR hv hW).2
  have hdAW : Disjoint A W := by
    apply Finset.disjoint_left.mpr
    intro Q hA hW
    exact (Finset.mem_sdiff.mp hA).2 hW
  have hd1 : Disjoint (T∪P) A := Finset.disjoint_union_left.mpr ⟨hdTA,hdPA⟩
  have hd2 : Disjoint (T∪P∪A) W := Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨hdTW,hdPW⟩,hdAW⟩
  have hsub : T∪P∪A∪W⊆U := by
    apply Finset.union_subset
    · apply Finset.union_subset
      · exact Finset.union_subset (fun Q hQ => (triplePair_properties (c:ℤ) (Ground N) H hH hroot hQ).1)
          (hPC.trans (covered_subset_pairUniverse (c:ℤ) (Ground N) H))
      · exact hAA.trans (available_subset_pairUniverse (c:ℤ) (Ground N) H)
    · exact fun Q hQ => (reserved_geometry N c L R I hc hLR hv hQ).1
  have hc0 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1,
    Finset.card_union_of_disjoint hdTP] at hc0
  rw [show T.card=(APTriples H).card from triplePairs_card (c:ℤ) H hroot] at hc0
  exact hc0

theorem actual_root_large_with_reservation (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hcore : 256*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hv : ValidIntervals N c L R I) (hlegal : Legal (Ground N) (H∪Intervals I))
    (hroot : Rooted H (c:ℤ)) (hw : CrookedWitnesses (c:ℤ) H (Reserved c N I)) :
    H.card+(Reserved c N I).card≤(APSmall H).card+(c-1)/2+
      (PairUniverse (c:ℤ) (Ground N)).card := by
  have hH : Legal (Ground N) H := ⟨fun S hS => hlegal.1 S (Finset.mem_union_left _ hS),
    fun S hS T hT he => hlegal.2 S (Finset.mem_union_left _ hS) T (Finset.mem_union_left _ hT) he⟩
  have hAP := actual_core_root_AP_card N c L R (APLarge H) hc hcL hLR hRN hcore
    (fun S hS => hH.1 S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2.1)
    (fun S hS => hroot S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2.2)
  have hC := crooked_outside_available_card hH hroot hw
  have hp := actual_root_resources_with_reservation N c L R H I hc hLR hv hlegal hroot
  have hf := family_partition H
  omega

theorem actual_interval_terminal_of_witnesses (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hcore : 256*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hv : ValidIntervals N c L R I) (hne : I.Nonempty)
    (hlegal : Legal (Ground N) (H∪Intervals I)) (hroot : Rooted H (c:ℤ))
    (hw : CrookedWitnesses (c:ℤ) H (Reserved c N I)) :
    (H∪Intervals I).card≤N.choose 2+1 := by
  have hr := actual_root_large_with_reservation N c L R H I hc hcL hLR hRN hcore hv hlegal hroot hw
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

theorem actual_interval_terminal_all_AP (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hcore : 256*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hv : ValidIntervals N c L R I) (hne : I.Nonempty)
    (hlegal : Legal (Ground N) (H∪Intervals I)) (hroot : Rooted H (c:ℤ))
    (hAP : ∀ S∈H, IsAP S) : (H∪Intervals I).card≤N.choose 2+1 := by
  apply actual_interval_terminal_of_witnesses N c L R H I hc hcL hLR hRN hcore hv hne hlegal hroot
  intro S hS hbad
  exact False.elim (hbad (hAP S hS))

theorem intrinsic_pair_of_completion_gap {c u v x : ℤ} {S : Finset ℤ}
    (hu : u∈S) (hv : v∈S) (huc : u≠c) (hvc : v≠c) (huv : u≠v)
    (hx : CompletionAt c u v x) (hxn : x∉S) : IntrinsicPair c S {u,v} := by
  refine ⟨by simp [huv],by simp [Ne.symm huc,Ne.symm hvc],
    Finset.insert_subset_iff.mpr ⟨hu,Finset.singleton_subset_iff.mpr hv⟩,?_⟩
  rintro ⟨T,hT,hcov,hTS⟩
  apply hxn
  exact hTS (completionAt_least hT (hcov (by simp)) (hcov (by simp)) (hcov (by simp)) hx)

theorem crooked_triples_have_reserved_avoiding_witnesses (N c L R : ℕ)
    (H : Finset (Finset ℤ)) (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hLR : L≤R)
    (hv : ValidIntervals N c L R I) (hlegal : Legal (Ground N) (H∪Intervals I))
    (hroot : Rooted H (c:ℤ)) (hsmall : ∀ S∈H, ¬IsAP S → S.card≤3) :
    CrookedWitnesses (c:ℤ) H (Reserved c N I) := by
  intro S hS hbad
  have hcS := hroot S hS
  have hcard : S.card=3 := by
    have hs := hsmall S hS hbad
    have hnot : ¬S.card≤2 := fun h2 => hbad (nonempty_card_le_two_isAP ⟨c,hcS⟩ h2)
    omega
  refine ⟨S.erase (c:ℤ),?_,root_triple_erase_not_reserved N c L R H I hc hLR hv hlegal hroot hS⟩
  refine ⟨by rw [Finset.card_erase_of_mem hcS,hcard],Finset.notMem_erase _ _,Finset.erase_subset _ _,?_⟩
  rintro ⟨T,hT,hST,hTS⟩
  rw [Finset.insert_erase hcS] at hST
  exact hbad ((Finset.Subset.antisymm hST hTS) ▸ hT)

theorem no_corner_crooked_have_reserved_avoiding_witnesses (N c L R : ℕ)
    (H : Finset (Finset ℤ)) (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hLR : L≤R)
    (hv : ValidIntervals N c L R I) (hroot : Rooted H (c:ℤ))
    (hgeom : ∀ S∈H, ¬IsAP S → ∀ u∈S, ∀ v∈S,
      ¬((c:ℤ)<u ∧ u<(L:ℤ) ∧ (R:ℤ)<v)) :
    CrookedWitnesses (c:ℤ) H (Reserved c N I) := by
  intro S hS hbad
  obtain ⟨u,hu,v,hvS,huc,hvc,huv,⟨x,hx,hxn⟩,_⟩ :=
    missing_completion_at_root_exists (hroot S hS) hbad
  have hQ := intrinsic_pair_of_completion_gap hu hvS huc hvc huv hx hxn
  refine ⟨{u,v},hQ,?_⟩
  intro hW
  obtain ⟨a,b,he,hca,haL,hRb⟩ := (reserved_geometry N c L R I hc hLR hv hW).2
  have ha : a∈S := hQ.2.2.1 (by rw [he]; simp)
  have hb : b∈S := hQ.2.2.1 (by rw [he]; simp)
  exact hgeom S hS hbad a ha b hb ⟨hca,haL,hRb⟩

theorem actual_interval_terminal_crooked_triples (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hcore : 256*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hv : ValidIntervals N c L R I) (hne : I.Nonempty)
    (hlegal : Legal (Ground N) (H∪Intervals I)) (hroot : Rooted H (c:ℤ))
    (hsmall : ∀ S∈H, ¬IsAP S → S.card≤3) : (H∪Intervals I).card≤N.choose 2+1 := by
  exact actual_interval_terminal_of_witnesses N c L R H I hc hcL hLR hRN hcore hv hne hlegal hroot
    (crooked_triples_have_reserved_avoiding_witnesses N c L R H I hc hLR hv hlegal hroot hsmall)

theorem actual_interval_terminal_no_crooked_corner (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hcore : 256*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hv : ValidIntervals N c L R I) (hne : I.Nonempty)
    (hlegal : Legal (Ground N) (H∪Intervals I)) (hroot : Rooted H (c:ℤ))
    (hgeom : ∀ S∈H, ¬IsAP S → ∀ u∈S, ∀ v∈S,
      ¬((c:ℤ)<u ∧ u<(L:ℤ) ∧ (R:ℤ)<v)) : (H∪Intervals I).card≤N.choose 2+1 := by
  exact actual_interval_terminal_of_witnesses N c L R H I hc hcL hLR hRN hcore hv hne hlegal hroot
    (no_corner_crooked_have_reserved_avoiding_witnesses N c L R H I hc hLR hv hroot hgeom)

theorem actual_avoider_interval_encoding (N c L R : ℕ) (G : Finset (Finset ℤ))
    (hi : ∀ S∈Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) :
    ∃ I : Finset (ℕ×ℕ), ValidIntervals N c L R I ∧
      Intervals I=Avoiders G (c:ℤ) ∧ G=RootPart G (c:ℤ)∪Intervals I := by
  let A := Avoiders G (c:ℤ)
  have hex : ∀ S : A, ∃ p : ℕ×ℕ,
      c<p.1 ∧ p.1≤L ∧ R≤p.2 ∧ p.2≤N ∧ S.val=Interval p := by
    intro S
    obtain ⟨a,b,hca,haL,hRb,hbN,he⟩ := hi S.val S.property
    exact ⟨(a,b),hca,haL,hRb,hbN,he⟩
  choose p hp using hex
  let I := Finset.univ.image p
  have hv : ValidIntervals N c L R I := by
    intro q hq
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(hp S).1,(hp S).2.1,(hp S).2.2.1,(hp S).2.2.2.1⟩
  have hIA : Intervals I=A := by
    ext S
    constructor
    · intro hS
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨T,_,rfl⟩ := Finset.mem_image.mp hq
      exact (hp T).2.2.2.2 ▸ T.property
    · intro hS
      exact Finset.mem_image.mpr ⟨p ⟨S,hS⟩,Finset.mem_image.mpr ⟨⟨S,hS⟩,Finset.mem_univ _,rfl⟩,
        (hp ⟨S,hS⟩).2.2.2.2.symm⟩
  refine ⟨I,hv,hIA,?_⟩
  rw [hIA]
  ext S
  simp only [RootPart,A,Avoiders,Finset.mem_union,Finset.mem_filter]
  tauto

theorem closed_at_left_neighbor_isAP {S : Finset ℤ} {c a : ℤ}
    (hc : c∈S) (ha : a∈S) (hac : a<c)
    (hnear : ∀ y∈S, y<c → y≤a)
    (hcl : ∀ w∈S, ∀ x, CompletionAt c a w x → x∈S) : IsAP S := by
  let d := (a-c).natAbs
  have had : (d:ℤ)=c-a := by
    dsimp [d]
    rw [show a-c=-(c-a) by omega,Int.natAbs_neg]
    exact Int.natAbs_of_nonneg (by omega)
  have hd : (0:ℤ)<d := by omega
  have hg : ∀ w∈S, Int.gcd (a-c) (w-c)=d := by
    intro w hw
    have hgpos : 0<Int.gcd (a-c) (w-c) := Int.gcd_pos_of_ne_zero_left _ (by omega)
    have hgle : Int.gcd (a-c) (w-c)≤d := Int.gcd_le_natAbs_left _ (by omega)
    have hgleZ : (Int.gcd (a-c) (w-c):ℤ)≤d := by exact_mod_cast hgle
    have hcomp : CompletionAt c a w (c-(Int.gcd (a-c) (w-c):ℤ)) := by
      unfold CompletionAt Completion
      refine ⟨by omega,by omega,?_⟩
      rw [show c-(Int.gcd (a-c) (w-c):ℤ)-c=-(Int.gcd (a-c) (w-c):ℤ) by omega]
      exact dvd_neg.mpr (dvd_refl _)
    have hmem := hcl w hw _ hcomp
    have hh := hnear _ hmem (by omega)
    omega
  have hne : S.Nonempty := ⟨c,hc⟩
  let lo := S.min' hne
  let hi := S.max' hne
  have hlo : lo∈S := Finset.min'_mem S hne
  have hhi : hi∈S := Finset.max'_mem S hne
  have hlo0 : lo≤c := Finset.min'_le S c hc
  have hhi0 : c≤hi := Finset.le_max' S c hc
  have hloa : lo≤a := Finset.min'_le S a ha
  have hhlo := hg lo hlo
  have hhhi := hg hi hhi
  refine ⟨d,c,hd,lo,hi,?_,hc⟩
  intro x
  constructor
  · intro hx
    exact ⟨Finset.min'_le S x hx,Finset.le_max' S x hx,by
      simpa only [hg x hx] using Int.gcd_dvd_right (a-c) (x-c)⟩
  · rintro ⟨hlx,hxh,hdx⟩
    by_cases hxc : x≤c
    · apply hcl lo hlo x
      unfold CompletionAt Completion
      exact ⟨by omega,by omega,by simpa only [hhlo] using hdx⟩
    · apply hcl hi hhi x
      unfold CompletionAt Completion
      exact ⟨by omega,by omega,by simpa only [hhhi] using hdx⟩

theorem crooked_left_neighbor_missing_completion {S : Finset ℤ} {c : ℤ}
    (hc : c∈S) (hbad : ¬IsAP S) (hleft : ∃ a∈S, a<c) :
    ∃ a∈S, ∃ v∈S, a<c ∧ v≠c ∧ a≠v ∧ ∃ x, CompletionAt c a v x ∧ x∉S := by
  let A := S.filter (fun x => x<c)
  have hA : A.Nonempty := by
    obtain ⟨a,ha,hac⟩ := hleft
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,hac⟩⟩
  let a := A.max' hA
  obtain ⟨ha,hac⟩ := Finset.mem_filter.mp (Finset.max'_mem A hA)
  have hnear : ∀ y∈S, y<c → y≤a := by
    intro y hy hyc
    exact Finset.le_max' A y (Finset.mem_filter.mpr ⟨hy,hyc⟩)
  have hn : ¬∀ w∈S, ∀ x, CompletionAt c a w x → x∈S := by
    intro hcl
    exact hbad (closed_at_left_neighbor_isAP hc ha hac hnear hcl)
  push Not at hn
  obtain ⟨v,hv,x,hx,hxn⟩ := hn
  have hbad3 : ¬IsAP ({c,a,v}:Finset ℤ) := by
    intro hAP
    have hm := completionAt_least hAP (by simp) (by simp) (by simp) hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl <;> contradiction
  have hvc : v≠c := by
    intro he; subst v
    exact hbad3 (by simpa using pair_isAP a c)
  have hav : a≠v := by
    intro he; subst v
    exact hbad3 (by simpa using pair_isAP c a)
  exact ⟨a,ha,v,hv,hac,hvc,hav,x,hx,hxn⟩

theorem left_crooked_has_reserved_avoiding_witness (N c L R : ℕ)
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hLR : L≤R) (hv : ValidIntervals N c L R I)
    {S : Finset ℤ} (hcS : (c:ℤ)∈S) (hbad : ¬IsAP S) (hleft : ∃ a∈S, a<(c:ℤ)) :
    ∃ Q, IntrinsicPair (c:ℤ) S Q ∧ Q∉Reserved c N I := by
  obtain ⟨a,ha,v,hvS,hac,hvc,hav,x,hx,hxn⟩ := crooked_left_neighbor_missing_completion hcS hbad hleft
  refine ⟨{a,v},intrinsic_pair_of_completion_gap ha hvS (by omega) hvc hav hx hxn,?_⟩
  intro hW
  obtain ⟨u,w,he,hcu,huL,hRw⟩ := (reserved_geometry N c L R I hc hLR hv hW).2
  have hh : a=u ∨ a=w := by
    simpa only [Finset.mem_insert,Finset.mem_singleton] using
      (show a∈({u,w}:Finset ℤ) by rw [←he]; simp)
  rcases hh with hh|hh <;> omega

theorem actual_interval_terminal_left_crooked (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hcore : 256*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hv : ValidIntervals N c L R I) (hne : I.Nonempty)
    (hlegal : Legal (Ground N) (H∪Intervals I)) (hroot : Rooted H (c:ℤ))
    (hleft : ∀ S∈H, ¬IsAP S → ∃ a∈S, a<(c:ℤ)) : (H∪Intervals I).card≤N.choose 2+1 := by
  apply actual_interval_terminal_of_witnesses N c L R H I hc hcL hLR hRN hcore hv hne hlegal hroot
  intro S hS hbad
  exact left_crooked_has_reserved_avoiding_witness N c L R I hc hLR hv (hroot S hS) hbad (hleft S hS hbad)

theorem actual_native_interval_terminal_crooked_triples (N c L R : ℕ)
    (G : Finset (Finset ℤ)) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hcore : 256*(L+N-R)*(Nat.log 2 N+1)≤N) (hlegal : Legal (Ground N) G)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hsmall : ∀ S∈RootPart G (c:ℤ), ¬IsAP S → S.card≤3) : G.card≤N.choose 2+1 := by
  obtain ⟨I,hv,hIA,hG⟩ := actual_avoider_interval_encoding N c L R G hi
  have hI : I.Nonempty := by
    obtain ⟨S,hS⟩ := hne
    rw [←hIA] at hS
    obtain ⟨p,hp,_⟩ := Finset.mem_image.mp hS
    exact ⟨p,hp⟩
  have hroot : Rooted (RootPart G (c:ℤ)) (c:ℤ) := fun S hS => (Finset.mem_filter.mp hS).2
  have hlegal' : Legal (Ground N) (RootPart G (c:ℤ)∪Intervals I) := hG ▸ hlegal
  rw [hG]
  exact actual_interval_terminal_crooked_triples N c L R (RootPart G (c:ℤ)) I
    hc hcL hLR hRN hcore hv hI hlegal' hroot hsmall

def GoodCrooked (c L R : ℕ) (S : Finset ℤ) : Prop :=
  S.card≤3 ∨ (∃ a∈S, a<(c:ℤ)) ∨
    (∀ u∈S, ∀ v∈S, ¬((c:ℤ)<u ∧ u<(L:ℤ) ∧ (R:ℤ)<v))

theorem good_crooked_reserved_avoiding_witnesses (N c L R : ℕ)
    (H : Finset (Finset ℤ)) (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hLR : L≤R)
    (hv : ValidIntervals N c L R I) (hlegal : Legal (Ground N) (H∪Intervals I))
    (hroot : Rooted H (c:ℤ)) (hgood : ∀ S∈H, ¬IsAP S → GoodCrooked c L R S) :
    CrookedWitnesses (c:ℤ) H (Reserved c N I) := by
  intro S hS hbad
  rcases hgood S hS hbad with hsmall|hleft|hgeom
  · have hcS := hroot S hS
    have hcard : S.card=3 := by
      have hnot : ¬S.card≤2 := fun h2 => hbad (nonempty_card_le_two_isAP ⟨c,hcS⟩ h2)
      omega
    refine ⟨S.erase (c:ℤ),?_,root_triple_erase_not_reserved N c L R H I hc hLR hv hlegal hroot hS⟩
    refine ⟨by rw [Finset.card_erase_of_mem hcS,hcard],Finset.notMem_erase _ _,Finset.erase_subset _ _,?_⟩
    rintro ⟨T,hT,hST,hTS⟩
    rw [Finset.insert_erase hcS] at hST
    exact hbad ((Finset.Subset.antisymm hST hTS) ▸ hT)
  · exact left_crooked_has_reserved_avoiding_witness N c L R I hc hLR hv (hroot S hS) hbad hleft
  · obtain ⟨u,hu,v,hvS,huc,hvc,huv,⟨x,hx,hxn⟩,_⟩ :=
      missing_completion_at_root_exists (hroot S hS) hbad
    have hQ := intrinsic_pair_of_completion_gap hu hvS huc hvc huv hx hxn
    refine ⟨{u,v},hQ,?_⟩
    intro hW
    obtain ⟨a,b,he,hca,haL,hRb⟩ := (reserved_geometry N c L R I hc hLR hv hW).2
    exact hgeom a (hQ.2.2.1 (by rw [he]; simp)) b (hQ.2.2.1 (by rw [he]; simp)) ⟨hca,haL,hRb⟩

theorem actual_native_interval_terminal_good_crooked (N c L R : ℕ)
    (G : Finset (Finset ℤ)) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hcore : 256*(L+N-R)*(Nat.log 2 N+1)≤N) (hlegal : Legal (Ground N) G)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hgood : ∀ S∈RootPart G (c:ℤ), ¬IsAP S → GoodCrooked c L R S) : G.card≤N.choose 2+1 := by
  obtain ⟨I,hv,hIA,hG⟩ := actual_avoider_interval_encoding N c L R G hi
  have hI : I.Nonempty := by
    obtain ⟨S,hS⟩ := hne
    rw [←hIA] at hS
    obtain ⟨p,hp,_⟩ := Finset.mem_image.mp hS
    exact ⟨p,hp⟩
  have hroot : Rooted (RootPart G (c:ℤ)) (c:ℤ) := fun S hS => (Finset.mem_filter.mp hS).2
  have hlegal' : Legal (Ground N) (RootPart G (c:ℤ)∪Intervals I) := hG ▸ hlegal
  have hw := good_crooked_reserved_avoiding_witnesses N c L R (RootPart G (c:ℤ)) I
    hc hLR hv hlegal' hroot hgood
  rw [hG]
  exact actual_interval_terminal_of_witnesses N c L R (RootPart G (c:ℤ)) I
    hc hcL hLR hRN hcore hv hI hlegal' hroot hw

#print axioms actual_avoider_interval_encoding
#print axioms actual_native_interval_terminal_crooked_triples
#print axioms good_crooked_reserved_avoiding_witnesses
#print axioms actual_native_interval_terminal_good_crooked
#print axioms closed_at_left_neighbor_isAP
#print axioms crooked_left_neighbor_missing_completion
#print axioms left_crooked_has_reserved_avoiding_witness
#print axioms actual_interval_terminal_left_crooked

#print axioms intrinsic_pair_of_completion_gap
#print axioms crooked_triples_have_reserved_avoiding_witnesses
#print axioms no_corner_crooked_have_reserved_avoiding_witnesses
#print axioms actual_interval_terminal_crooked_triples
#print axioms actual_interval_terminal_no_crooked_corner

#print axioms intrinsic_pair_private
#print axioms crooked_outside_available_card
#print axioms core_APLarge_subset_covered
#print axioms actual_root_resources_with_reservation
#print axioms actual_root_large_with_reservation
#print axioms actual_interval_terminal_of_witnesses
#print axioms actual_interval_terminal_all_AP
#print axioms ordered_pair_injective
#print axioms interval_injective_on
#print axioms intervals_card
#print axioms reserved_injective_on
#print axioms reserved_card_partition
#print axioms reserved_geometry
#print axioms legal_root_interval_between
#print axioms root_triple_erase_not_reserved
#print axioms boundary_code_bounds
#print axioms boundary_code_injective
#print axioms legal_interval_meet
#print axioms actual_small_boundary_payment
end
end JSP233.LongTerminal35
