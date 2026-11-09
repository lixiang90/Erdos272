module

public import Erdos272.Geometry.CrossLine30
public import Erdos272.Resources.StarBoundConcrete30
public import Mathlib.Combinatorics.Hall.Finite

@[expose] public section

/-! Genuine Hall matchings from the all-subfamily AP defect theorem.
Resources remain actual internal primitive bad pairs, with one optional dummy. -/
namespace JSP233.StepHall33
open StarCompletion StaircaseGeometry AffineLine30 CrossLine30
open scoped Classical
open scoped BigOperators
noncomputable section

theorem row_image_subset {α : Type*} [DecidableEq α] (F : Finset α)
    (I : Finset F) : I.image Subtype.val⊆F := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  exact y.property

theorem row_biUnion_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (I : Finset F) (t : α→Finset β) :
    I.biUnion (fun S => t S.val)=(I.image Subtype.val).biUnion t := by
  ext b
  simp only [Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨x,hx,hb⟩
    exact ⟨x.val,⟨x,hx,rfl⟩,hb⟩
  · rintro ⟨a,⟨x,hx,rfl⟩,hb⟩
    exact ⟨x,hx,hb⟩

theorem dummy_biUnion_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (I : Finset F) (t : α→Finset β) (hne : I.Nonempty) :
    I.biUnion (fun S => insert none ((t S.val).image some))=
      insert none (((I.image Subtype.val).biUnion t).image some) := by
  rw [←row_biUnion_eq F I t]
  ext q
  cases q with
  | none =>
    constructor
    · intro h; simp
    · intro h
      obtain ⟨x,hx⟩ := hne
      exact Finset.mem_biUnion.mpr ⟨x,hx,by simp⟩
  | some b =>
    simp only [Finset.mem_biUnion,Finset.mem_insert,Option.some_ne_none,false_or,
      Finset.mem_image,Option.some.injEq]
    aesop

theorem hall_without_dummy {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (t : α→Finset β)
    (hcount : ∀ T⊆F, T.card≤(T.biUnion t).card) :
    ∃ f : F→β, Function.Injective f ∧ ∀ S, f S∈t S.val := by
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' (fun S : F => t S.val)).mp
  intro I
  have hh := hcount (I.image Subtype.val) (row_image_subset F I)
  rw [Finset.card_image_of_injective I Subtype.val_injective,←row_biUnion_eq F I t] at hh
  exact hh

theorem hall_with_dummy {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (t : α→Finset β)
    (hcount : ∀ T⊆F, T.card≤(T.biUnion t).card+1) :
    ∃ f : F→Option β, Function.Injective f ∧
      ∀ S, f S∈insert none ((t S.val).image some) := by
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun S : F => insert none ((t S.val).image some))).mp
  intro I
  by_cases hne : I.Nonempty
  · rw [dummy_biUnion_eq F I t hne,
      Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (Option.some_injective β)]
    have hh := hcount (I.image Subtype.val) (row_image_subset F I)
    rwa [Finset.card_image_of_injective I Subtype.val_injective] at hh
  · have he : I=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he]

theorem actual_step_subfamily_hall (c d : ℤ) (hd : 0<d)
    (F : Finset (Finset ℤ))
    (hF : ∀ S∈F, ∃ l r : ℕ, S=mapSet c d (Window l r) ∧ 4≤S.card) :
    ∀ T⊆F, T.card≤(T.biUnion (gcdStepPairs c d)).card+1 := by
  intro T hT
  have hh := fixed_step_defect_le_one c d hd T (fun S hS => hF S (hT hS))
  change (T.card:ℤ)-((T.biUnion (gcdStepPairs c d)).card:ℤ)≤1 at hh
  omega

theorem actual_step_matching (c d : ℤ) (hd : 0<d)
    (F : Finset (Finset ℤ))
    (hF : ∀ S∈F, ∃ l r : ℕ, S=mapSet c d (Window l r) ∧ 4≤S.card) :
    ∃ f : F→Option (Finset ℤ), Function.Injective f ∧
      ∀ S, f S=none ∨ ∃ Q, f S=some Q ∧ Q⊆S.val ∧ IsStepPrimitive c d Q := by
  obtain ⟨f,hf,hmem⟩ := hall_with_dummy F (gcdStepPairs c d)
    (actual_step_subfamily_hall c d hd F hF)
  refine ⟨f,hf,?_⟩
  intro S
  rcases Finset.mem_insert.mp (hmem S) with he | he
  · exact Or.inl he
  · obtain ⟨Q,hQ,he⟩ := Finset.mem_image.mp he
    obtain ⟨hsub,hprim⟩ := (mem_gcdStepPairs c d S.val Q).mp hQ
    exact Or.inr ⟨Q,he.symm,hsub,hprim⟩

theorem actual_left_thin_matching (c d : ℤ) (hd : 0<d)
    (F : Finset (Finset ℤ))
    (hF : ∀ S∈F, ∃ l r : ℕ, S=mapSet c d (Window l r) ∧ 4≤S.card ∧ l≤1) :
    ∃ f : F→Finset ℤ, Function.Injective f ∧
      ∀ S, f S⊆S.val ∧ IsStepPrimitive c d (f S) := by
  obtain ⟨f,hf,hmem⟩ := hall_without_dummy F (gcdStepPairs c d) (by
    intro T hT
    have hh := fixed_step_left_thin_defect_nonpos c d hd T (fun S hS => hF S (hT hS))
    change (T.card:ℤ)-((T.biUnion (gcdStepPairs c d)).card:ℤ)≤0 at hh
    omega)
  exact ⟨f,hf,fun S => (mem_gcdStepPairs c d S.val (f S)).mp (hmem S)⟩

theorem actual_right_thin_matching (c d : ℤ) (hd : 0<d)
    (F : Finset (Finset ℤ))
    (hF : ∀ S∈F, ∃ l r : ℕ, S=mapSet c d (Window l r) ∧ 4≤S.card ∧ r≤1) :
    ∃ f : F→Finset ℤ, Function.Injective f ∧
      ∀ S, f S⊆S.val ∧ IsStepPrimitive c d (f S) := by
  obtain ⟨f,hf,hmem⟩ := hall_without_dummy F (gcdStepPairs c d) (by
    intro T hT
    have hh := fixed_step_right_thin_defect_nonpos c d hd T (fun S hS => hF S (hT hS))
    change (T.card:ℤ)-((T.biUnion (gcdStepPairs c d)).card:ℤ)≤0 at hh
    omega)
  exact ⟨f,hf,fun S => (mem_gcdStepPairs c d S.val (f S)).mp (hmem S)⟩

theorem dummy_rows_card_le_one {α β : Type*} [Fintype α] [DecidableEq α]
    (f : α→Option β) (hinj : Function.Injective f) :
    ((Finset.univ : Finset α).filter (fun x => f x=none)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  apply hinj
  exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm

def ExteriorPair (c L R : ℤ) (Q : Finset ℤ) : Prop :=
  ∃ u v : ℤ, Q={u,v} ∧ c<u ∧ u<L ∧ R<v

theorem upper_bounded_pair_not_exterior (c L R : ℤ) (S Q : Finset ℤ)
    (hQ : Q⊆S) (hupper : ∀ x∈S, x≤R) : ¬ExteriorPair c L R Q := by
  rintro ⟨u,v,hrep,hcu,huL,hRv⟩
  have hv : v∈Q := by rw [hrep]; simp
  have hh := hupper v (hQ hv)
  omega

theorem actual_short_step_matching (c d L R : ℤ) (hd : 0<d)
    (F : Finset (Finset ℤ))
    (hF : ∀ S∈F, ∃ l r : ℕ, S=mapSet c d (Window l r) ∧ 4≤S.card)
    (hupper : ∀ S∈F, ∀ x∈S, x≤R) :
    ∃ f : F→Option (Finset ℤ), Function.Injective f ∧
      ∀ S, f S=none ∨ ∃ Q, f S=some Q ∧ Q⊆S.val ∧
        IsStepPrimitive c d Q ∧ ¬ExteriorPair c L R Q := by
  obtain ⟨f,hf,hm⟩ := actual_step_matching c d hd F hF
  refine ⟨f,hf,?_⟩
  intro S
  rcases hm S with hn | ⟨Q,he,hsub,hprim⟩
  · exact Or.inl hn
  · exact Or.inr ⟨Q,he,hsub,hprim,
      upper_bounded_pair_not_exterior c L R S.val Q hsub (hupper S.val S.property)⟩

theorem large_step_pair_not_exterior (c d L R : ℤ) (hd : 0<d) (hgap : L-c<d)
    (S Q : Finset ℤ) (hS : ∃ l r : ℕ, S=mapSet c d (Window l r))
    (hQ : Q⊆S) : ¬ExteriorPair c L R Q := by
  rintro ⟨u,v,hrep,hcu,huL,hRv⟩
  have hu : u∈S := hQ (by rw [hrep]; simp)
  obtain ⟨l,r,rfl⟩ := hS
  have hc : c∈mapSet c d (Window l r) := by
    apply Finset.mem_image.mpr
    exact ⟨0,zero_mem_window l r,by simp [affine]⟩
  have hdvd := APGeometry.apAt_dvd_sub (mapWindow_APAt c d hd l r) hc hu
  have hz : u-c=0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hdvd
  omega

theorem actual_large_step_matching (c d L R : ℤ) (hd : 0<d) (hgap : L-c<d)
    (F : Finset (Finset ℤ))
    (hF : ∀ S∈F, ∃ l r : ℕ, S=mapSet c d (Window l r) ∧ 4≤S.card) :
    ∃ f : F→Option (Finset ℤ), Function.Injective f ∧
      ∀ S, f S=none ∨ ∃ Q, f S=some Q ∧ Q⊆S.val ∧
        IsStepPrimitive c d Q ∧ ¬ExteriorPair c L R Q := by
  obtain ⟨f,hf,hm⟩ := actual_step_matching c d hd F hF
  refine ⟨f,hf,?_⟩
  intro S
  rcases hm S with hn | ⟨Q,he,hsub,hprim⟩
  · exact Or.inl hn
  · obtain ⟨l,r,hrep,hlarge⟩ := hF S.val S.property
    exact Or.inr ⟨Q,he,hsub,hprim,
      large_step_pair_not_exterior c d L R hd hgap S.val Q ⟨l,r,hrep⟩ hsub⟩

theorem physical_left_thin (N : ℕ) (c d : ℤ) (hd : 0<d)
    (hsmall : c-1<2*d) (S : Finset ℤ) (hground : S⊆Ground N)
    {l r : ℕ} (hS : S=mapSet c d (Window l r)) : l≤1 := by
  have hx : c-d*(l:ℤ)∈S := by
    rw [hS]
    refine Finset.mem_image.mpr ⟨-(l:ℤ),by simp [Window],?_⟩
    dsimp [affine]; ring
  have hb := ((mem_ground N _).mp (hground hx)).1
  by_contra hn
  have hl : (2:ℤ)≤l := by omega
  nlinarith

theorem actual_step_matching_with_dummy_geometry (N : ℕ) (c d : ℤ) (hd : 0<d)
    (F : Finset (Finset ℤ)) (hground : ∀ S∈F, S⊆Ground N)
    (hF : ∀ S∈F, ∃ l r : ℕ, S=mapSet c d (Window l r) ∧ 4≤S.card) :
    ∃ f : F→Option (Finset ℤ), Function.Injective f ∧
      (∀ S, f S=none → 2*d≤c-1) ∧
      ∀ S, f S=none ∨ ∃ Q, f S=some Q ∧ Q⊆S.val ∧ IsStepPrimitive c d Q := by
  by_cases hthick : 2*d≤c-1
  · obtain ⟨f,hf,hm⟩ := actual_step_matching c d hd F hF
    exact ⟨f,hf,fun _ _ => hthick,hm⟩
  · have hthin : ∀ S∈F, ∃ l r : ℕ, S=mapSet c d (Window l r) ∧ 4≤S.card ∧ l≤1 := by
      intro S hS
      obtain ⟨l,r,he,hcard⟩ := hF S hS
      exact ⟨l,r,he,hcard,physical_left_thin N c d hd (by omega) S (hground S hS) he⟩
    obtain ⟨f,hf,hm⟩ := actual_left_thin_matching c d hd F hthin
    refine ⟨fun S => some (f S),?_,?_,?_⟩
    · exact (Option.some_injective (Finset ℤ)).comp hf
    · intro S hs; simp at hs
    · intro S
      exact Or.inr ⟨f S,rfl,(hm S).1,(hm S).2⟩

theorem graded_hall_count {α κ β : Type*} [DecidableEq α] [DecidableEq κ]
    [DecidableEq β] (F : Finset α) (key : α→κ) (pool : κ→Finset β)
    (hdis : ∀ i∈F.image key, ∀ j∈F.image key, i≠j → Disjoint (pool i) (pool j))
    (hcap : ∀ i∈F.image key, (F.filter (fun x => key x=i)).card≤(pool i).card) :
    ∀ T⊆F, T.card≤(T.biUnion (fun x => pool (key x))).card := by
  intro T hTF
  have hfilter : T.filter (fun x => key x∈T.image key)=T := by
    apply Finset.filter_true_of_mem
    intro x hx
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  have hfib := Finset.sum_card_fiberwise_eq_card_filter T (T.image key) key
  rw [hfilter] at hfib
  have hi : T.image key⊆F.image key := Finset.image_subset_image hTF
  have hs : (∑ i∈T.image key, (T.filter (fun x => key x=i)).card)≤
      ∑ i∈T.image key, (pool i).card := by
    apply Finset.sum_le_sum
    intro i hI
    have hsub : T.filter (fun x => key x=i)⊆F.filter (fun x => key x=i) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨hTF (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
    exact (Finset.card_le_card hsub).trans (hcap i (hi hI))
  have hu : (T.image key).biUnion pool=T.biUnion (fun x => pool (key x)) := by
    ext b
    simp only [Finset.mem_biUnion,Finset.mem_image]
    aesop
  have hc : ((T.image key).biUnion pool).card=∑ i∈T.image key, (pool i).card := by
    apply Finset.card_biUnion
    intro i hI j hJ hne
    exact hdis i (hi hI) j (hi hJ) hne
  rw [hfib] at hs
  rwa [←hc,hu] at hs

theorem graded_hall_matching {α κ β : Type*} [DecidableEq α] [DecidableEq κ]
    [DecidableEq β] (F : Finset α) (key : α→κ) (pool : κ→Finset β)
    (hdis : ∀ i∈F.image key, ∀ j∈F.image key, i≠j → Disjoint (pool i) (pool j))
    (hcap : ∀ i∈F.image key, (F.filter (fun x => key x=i)).card≤(pool i).card) :
    ∃ f : F→β, Function.Injective f ∧ ∀ S, f S∈pool (key S.val) :=
  hall_without_dummy F (fun x => pool (key x)) (graded_hall_count F key pool hdis hcap)

def RowResidues (A r : ℕ) : Finset ℕ :=
  (Finset.range r).filter (fun a => A≤a ∧ Nat.Coprime r a)

def PositiveRowPool (A r : ℕ) : Finset (Finset ℤ) :=
  (RowResidues A r).image (fun a : ℕ => {(a:ℤ),(r:ℤ)})

theorem row_residue_card (A r : ℕ) :
    Nat.totient r≤(RowResidues A r).card+A := by
  let all := (Finset.range r).filter (fun a => Nat.Coprime r a)
  have hsub : all⊆RowResidues A r∪Finset.range A := by
    intro a ha
    obtain ⟨har,hcop⟩ := Finset.mem_filter.mp ha
    by_cases hAa : A≤a
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨har,hAa,hcop⟩)
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr (by omega))
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa only [all,Nat.totient_eq_card_coprime,Finset.card_range] using hh

theorem positive_row_pool_card (A r : ℕ) :
    (PositiveRowPool A r).card=(RowResidues A r).card := by
  unfold PositiveRowPool
  apply Finset.card_image_iff.mpr
  intro a ha b hb heq
  have har := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hbr := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have hh := StaircaseSupply.ordered_pair_ext (by omega : (a:ℤ)<r)
    (by omega : (b:ℤ)<r) heq
  exact_mod_cast hh.1

theorem positive_row_pools_disjoint (A r s : ℕ) (hne : r≠s) :
    Disjoint (PositiveRowPool A r) (PositiveRowPool A s) := by
  apply Finset.disjoint_left.mpr
  intro Q hQ hQ'
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hQ'
  have har := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hbs := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have hh := StaircaseSupply.ordered_pair_ext (by omega : (b:ℤ)<s)
    (by omega : (a:ℤ)<r) he
  exact hne (by exact_mod_cast hh.2.symm)

theorem row_fibre_card (C : Finset (ℕ×ℕ)) (H r : ℕ)
    (hleft : ∀ p∈C, p.1≤H) :
    (C.filter (fun p => p.2=r)).card≤H+1 := by
  have hinj : Set.InjOn (fun p : ℕ×ℕ => p.1) (C.filter (fun p => p.2=r)) := by
    intro p hp q hq he
    apply Prod.ext he
    exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  have hsub : (C.filter (fun p => p.2=r)).image Prod.fst⊆Finset.range (H+1) := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_range.mpr (by have hh := hleft p (Finset.mem_filter.mp hp).1; omega)
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj,Finset.card_range] at hh
  exact hh

theorem actual_long_row_matching (C : Finset (ℕ×ℕ)) (A H : ℕ)
    (hA : 1≤A) (hleft : ∀ p∈C, p.1≤H) (hlong : ∀ p∈C, 3≤p.2)
    (hphi : ∀ p∈C, A+H+1≤Nat.totient p.2) :
    ∃ f : C→Finset ℤ, Function.Injective f ∧
      ∀ p, f p⊆Window p.val.1 p.val.2 ∧ IsPrimitiveBadPair (f p) ∧
        ∀ x∈f p, (A:ℤ)≤x := by
  obtain ⟨f,hf,hm⟩ := graded_hall_matching C Prod.snd (PositiveRowPool A)
    (fun r _ s _ hne => positive_row_pools_disjoint A r s hne) (by
      intro r hr
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
      have hc := row_fibre_card C H p.2 hleft
      have hres := row_residue_card A p.2
      have htot := hphi p hp
      rw [positive_row_pool_card]
      omega)
  refine ⟨f,hf,?_⟩
  intro p
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp (hm p)
  obtain ⟨har,hAa,hcop⟩ := Finset.mem_filter.mp ha
  have har' := Finset.mem_range.mp har
  rw [←he]
  refine ⟨?_,?_,?_⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [Window,Finset.mem_Icc] <;> omega
  · exact (StaircaseSupply.positive_pair_iff p.val.2 a (by omega) har').mpr
      ⟨hcop.symm,hlong p.val p.property⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> omega

theorem actual_affine_long_row_matching (C : Finset (ℕ×ℕ)) (A H : ℕ)
    (c d L R : ℤ) (hd : 0<d) (hA : 1≤A)
    (hleft : ∀ p∈C, p.1≤H) (hlong : ∀ p∈C, 3≤p.2)
    (hphi : ∀ p∈C, A+H+1≤Nat.totient p.2) (hL : L≤c+d*A) :
    ∃ f : C→Finset ℤ, Function.Injective f ∧
      ∀ p, f p⊆mapSet c d (Window p.val.1 p.val.2) ∧
        IsStepPrimitive c d (f p) ∧ ¬ExteriorPair c L R (f p) := by
  obtain ⟨g,hg,hm⟩ := actual_long_row_matching C A H hA hleft hlong hphi
  refine ⟨fun p => mapSet c d (g p),(mapSet_injective c d hd).comp hg,?_⟩
  intro p
  refine ⟨(mapSet_subset_iff c d hd _ _).mpr (hm p).1,
    (isStepPrimitive_map_iff c d hd _).mpr (hm p).2.1,?_⟩
  rintro ⟨u,v,he,hcu,huL,hRv⟩
  dsimp only at he
  have hu : u∈mapSet c d (g p) := by rw [he]; simp
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
  have hAx := (hm p).2.2 x hx
  dsimp [affine] at huL
  have hmul := mul_le_mul_of_nonneg_left hAx hd.le
  linarith

theorem reserve_biUnion_eq {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] (F : Finset α) (I : Finset F) (t : α→Finset β)
    (R : Finset γ) (hne : I.Nonempty) :
    I.biUnion (fun S => (R.image (Sum.inl : γ→γ⊕β))∪(t S.val).image Sum.inr)=
      (R.image Sum.inl)∪(((I.image Subtype.val).biUnion t).image Sum.inr) := by
  rw [←row_biUnion_eq F I t]
  obtain ⟨x,hx⟩ := hne
  ext q
  cases q with
  | inl a => simp; aesop
  | inr b => simp

theorem hall_with_reserve {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] (F : Finset α) (t : α→Finset β) (R : Finset γ)
    (hcount : ∀ T⊆F, T.card≤(T.biUnion t).card+R.card) :
    ∃ f : F→γ⊕β, Function.Injective f ∧
      ∀ S, (∃ a∈R, f S=Sum.inl a) ∨ ∃ q∈t S.val, f S=Sum.inr q := by
  have hhall : ∀ I : Finset F,
      I.card≤(I.biUnion (fun S => (R.image (Sum.inl : γ→γ⊕β))∪
        (t S.val).image Sum.inr)).card := by
    intro I
    by_cases hne : I.Nonempty
    · rw [reserve_biUnion_eq F I t R hne]
      have hdis : Disjoint (R.image (Sum.inl : γ→γ⊕β))
          (((I.image Subtype.val).biUnion t).image Sum.inr) := by
        apply Finset.disjoint_left.mpr
        intro q hq hq'
        obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨b,_,he⟩ := Finset.mem_image.mp hq'
        exact Sum.inr_ne_inl he
      rw [Finset.card_union_of_disjoint hdis,
        Finset.card_image_of_injective _ Sum.inl_injective,
        Finset.card_image_of_injective _ Sum.inr_injective]
      have hh := hcount (I.image Subtype.val) (row_image_subset F I)
      rw [Finset.card_image_of_injective I Subtype.val_injective] at hh
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  obtain ⟨f,hf,hm⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun S : F => (R.image (Sum.inl : γ→γ⊕β))∪(t S.val).image Sum.inr)).mp hhall
  refine ⟨f,hf,?_⟩
  intro S
  rcases Finset.mem_union.mp (hm S) with h | h
  · obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h
    exact Or.inl ⟨a,ha,he.symm⟩
  · obtain ⟨q,hq,he⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨q,hq,he.symm⟩

theorem actual_pool_eq_biUnion (c : ℤ) (F : Finset (Finset ℤ)) :
    APResourcePool c F=F.biUnion (fun S => gcdStepPairs c (trueStep c S) S) := by
  ext Q
  simp only [APResourcePool,AllStepPool,StepLabels,Finset.mem_biUnion,Finset.mem_image,
    gcdStepPool,StepClass,Finset.mem_filter]
  constructor
  · rintro ⟨d,_,S,⟨hS,he⟩,hQ⟩
    exact ⟨S,hS,he ▸ hQ⟩
  · rintro ⟨S,hS,hQ⟩
    exact ⟨trueStep c S,⟨S,hS,rfl⟩,S,⟨hS,rfl⟩,hQ⟩

theorem actual_active_steps_mono (c : ℤ) {F G : Finset (Finset ℤ)} (hFG : F⊆G) :
    APActiveSteps c F⊆APActiveSteps c G := by
  intro d hd
  obtain ⟨hdlabel,⟨S,hS,hs⟩,T,hT,ht⟩ := Finset.mem_filter.mp hd
  obtain ⟨U,hU,he⟩ := Finset.mem_image.mp hdlabel
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨U,hFG hU,he⟩,
    ⟨S,Finset.mem_filter.mpr ⟨hFG (Finset.mem_filter.mp hS).1,(Finset.mem_filter.mp hS).2⟩,hs⟩,
    T,Finset.mem_filter.mpr ⟨hFG (Finset.mem_filter.mp hT).1,(Finset.mem_filter.mp hT).2⟩,ht⟩

theorem actual_multistep_matching (c : ℤ) (F : Finset (Finset ℤ))
    (hAP : ∀ S∈F, IsAP S) (hroot : Rooted F c) (hlarge : ∀ S∈F, 4≤S.card) :
    ∃ f : F→ℤ⊕Finset ℤ, Function.Injective f ∧
      ∀ S, (∃ d∈APActiveSteps c F, f S=Sum.inl d) ∨
        ∃ Q, f S=Sum.inr Q ∧ Q⊆S.val ∧ IsStepPrimitive c (trueStep c S.val) Q := by
  obtain ⟨f,hf,hm⟩ := hall_with_reserve F (fun S => gcdStepPairs c (trueStep c S) S)
    (APActiveSteps c F) (by
      intro T hTF
      have hh := actual_AP_family_count c T (fun S hS => hAP S (hTF hS))
        (fun S hS => hroot S (hTF hS)) (fun S hS => hlarge S (hTF hS))
      rw [actual_pool_eq_biUnion] at hh
      exact hh.trans (Nat.add_le_add_left
        (Finset.card_le_card (actual_active_steps_mono c hTF)) _))
  refine ⟨f,hf,?_⟩
  intro S
  rcases hm S with h | ⟨Q,hQ,he⟩
  · exact Or.inl h
  · obtain ⟨hs,hp⟩ := (mem_gcdStepPairs c (trueStep c S.val) S.val Q).mp hQ
    exact Or.inr ⟨Q,he,hs,hp⟩

theorem actual_multistep_physical_matching (N : ℕ) (c : ℤ)
    (F : Finset (Finset ℤ)) (hground : ∀ S∈F, S⊆Ground N)
    (hAP : ∀ S∈F, IsAP S) (hroot : Rooted F c) (hlarge : ∀ S∈F, 4≤S.card) :
    ∃ f : F→ℤ⊕Finset ℤ, Function.Injective f ∧
      ∀ S, (∃ d∈APActiveSteps c F, f S=Sum.inl d ∧ 0<d ∧
        1≤c-2*d ∧ c+2*d≤N) ∨
        ∃ Q, f S=Sum.inr Q ∧ Q⊆S.val ∧ IsStepPrimitive c (trueStep c S.val) Q := by
  obtain ⟨f,hf,hm⟩ := actual_multistep_matching c F hAP hroot hlarge
  refine ⟨f,hf,?_⟩
  intro S
  rcases hm S with ⟨d,hd,he⟩ | h
  · have hg := active_step_geometry c (Ground N) F hAP hroot hground hd
    exact Or.inl ⟨d,hd,he,hg.1,((mem_ground N _).mp hg.2.1).1,
      ((mem_ground N _).mp hg.2.2).2⟩
  · exact Or.inr h

#print axioms row_image_subset
#print axioms row_biUnion_eq
#print axioms dummy_biUnion_eq
#print axioms hall_without_dummy
#print axioms hall_with_dummy
#print axioms actual_step_subfamily_hall
#print axioms actual_step_matching
#print axioms actual_left_thin_matching
#print axioms actual_right_thin_matching
#print axioms dummy_rows_card_le_one
#print axioms upper_bounded_pair_not_exterior
#print axioms actual_short_step_matching
#print axioms large_step_pair_not_exterior
#print axioms actual_large_step_matching
#print axioms physical_left_thin
#print axioms actual_step_matching_with_dummy_geometry
#print axioms graded_hall_count
#print axioms graded_hall_matching
#print axioms row_residue_card
#print axioms positive_row_pool_card
#print axioms positive_row_pools_disjoint
#print axioms row_fibre_card
#print axioms actual_long_row_matching
#print axioms actual_affine_long_row_matching
#print axioms reserve_biUnion_eq
#print axioms hall_with_reserve
#print axioms actual_pool_eq_biUnion
#print axioms actual_active_steps_mono
#print axioms actual_multistep_matching
#print axioms actual_multistep_physical_matching
end
end JSP233.StepHall33
