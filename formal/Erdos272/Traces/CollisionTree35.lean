module

public import Erdos272.Capacity.AnchorCapacity33
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-! Finite global-component collision decomposition.
The construction starts from any actual finpartition, selects a maximal-rank
cross-block meet, and merges every block meeting its upper cone. Each selected
block contributes one representative to a genuine meet clique. Strong induction
on the number of blocks constructs the decomposition and its exact net fee.
No clique packing or total-fee identity is an input to that construction. -/
namespace JSP233.CollisionTree35
open scoped Classical BigOperators
noncomputable section

variable {α : Type*} [DecidableEq α] {A : Finset α}

def MergeParts (P : Finpartition A) (C : Finset (Finset α)) : Finset (Finset α) :=
  insert (C.biUnion id) (P.parts \ C)

theorem merge_union_nonempty (P : Finpartition A) {C : Finset (Finset α)}
    (hC : C⊆P.parts) (hne : C.Nonempty) : (C.biUnion id).Nonempty := by
  obtain ⟨B,hB⟩ := hne
  obtain ⟨x,hx⟩ := P.nonempty_of_mem_parts (hC hB)
  exact ⟨x,Finset.mem_biUnion.mpr ⟨B,hB,hx⟩⟩

theorem merge_union_not_mem (P : Finpartition A) {C : Finset (Finset α)}
    (hC : C⊆P.parts) (hne : C.Nonempty) : C.biUnion id∉P.parts\C := by
  intro hh
  obtain ⟨hU,hnot⟩ := Finset.mem_sdiff.mp hh
  obtain ⟨B,hB⟩ := hne
  obtain ⟨x,hx⟩ := P.nonempty_of_mem_parts (hC hB)
  have he := P.eq_of_mem_parts hU (hC hB)
    (Finset.mem_biUnion.mpr ⟨B,hB,hx⟩) hx
  exact hnot (he.symm ▸ hB)

theorem merge_parts_unique (P : Finpartition A) {C : Finset (Finset α)}
    (hC : C⊆P.parts) (_hne : C.Nonempty) :
    ∀ x∈A, ∃! B∈MergeParts P C, x∈B := by
  intro x hx
  obtain ⟨B,hB,hxB⟩ := P.exists_mem hx
  by_cases hBC : B∈C
  · have hxU : x∈C.biUnion id := Finset.mem_biUnion.mpr ⟨B,hBC,hxB⟩
    refine ⟨C.biUnion id,⟨Finset.mem_insert_self _ _,hxU⟩,?_⟩
    rintro T ⟨hT,hxT⟩
    rcases Finset.mem_insert.mp hT with rfl | hT
    · rfl
    · obtain ⟨hTP,hTC⟩ := Finset.mem_sdiff.mp hT
      exact False.elim (hTC ((P.eq_of_mem_parts hTP hB hxT hxB).symm ▸ hBC))
  · refine ⟨B,⟨Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hB,hBC⟩),hxB⟩,?_⟩
    rintro T ⟨hT,hxT⟩
    rcases Finset.mem_insert.mp hT with rfl | hT
    · obtain ⟨U,hU,hxU⟩ := Finset.mem_biUnion.mp hxT
      exact False.elim (hBC ((P.eq_of_mem_parts hB (hC hU) hxB hxU).symm ▸ hU))
    · exact P.eq_of_mem_parts (Finset.mem_sdiff.mp hT).1 hB hxT hxB

def Merge (P : Finpartition A) (C : Finset (Finset α))
    (hC : C⊆P.parts) (hne : C.Nonempty) : Finpartition A :=
  Finpartition.ofExistsUnique (MergeParts P C)
    (by
      intro B hB x hx
      rcases Finset.mem_insert.mp hB with rfl | hB
      · obtain ⟨T,hT,hxT⟩ := Finset.mem_biUnion.mp hx
        exact P.subset (hC hT) hxT
      · exact P.subset (Finset.mem_sdiff.mp hB).1 hx)
    (merge_parts_unique P hC hne)
    (by
      intro hh
      rcases Finset.mem_insert.mp hh with hh | hh
      · exact (merge_union_nonempty P hC hne).ne_empty hh.symm
      · exact P.empty_notMem_parts (Finset.mem_sdiff.mp hh).1)

theorem merge_parts (P : Finpartition A) {C : Finset (Finset α)}
    (hC : C⊆P.parts) (hne : C.Nonempty) :
    (Merge P C hC hne).parts=MergeParts P C := rfl

theorem merge_card (P : Finpartition A) {C : Finset (Finset α)}
    (hC : C⊆P.parts) (hne : C.Nonempty) :
    (Merge P C hC hne).parts.card=P.parts.card-C.card+1 := by
  rw [merge_parts,MergeParts,Finset.card_insert_of_notMem (merge_union_not_mem P hC hne),
    Finset.card_sdiff_of_subset hC]

theorem merge_coarser (P : Finpartition A) {C : Finset (Finset α)}
    (hC : C⊆P.parts) (hne : C.Nonempty) : P≤Merge P C hC hne := by
  intro B hB
  by_cases hBC : B∈C
  · refine ⟨C.biUnion id,Finset.mem_insert_self _ _,?_⟩
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨B,hBC,hx⟩
  · exact ⟨B,Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hB,hBC⟩),le_rfl⟩

theorem merge_fee (P : Finpartition A) {C : Finset (Finset α)}
    (hC : C⊆P.parts) (hne : C.Nonempty) :
    (C.card-1)+(Merge P C hC hne).parts.card=P.parts.card := by
  have hc := Finset.card_le_card hC
  have hp := hne.card_pos
  rw [merge_card P hC hne]
  omega

theorem merge_strict (P : Finpartition A) {C : Finset (Finset α)}
    (hC : C⊆P.parts) (h2 : 2≤C.card) :
    (Merge P C hC (by exact Finset.card_pos.mp (by omega))).parts.card<P.parts.card := by
  rw [merge_card]
  have hc := Finset.card_le_card hC
  omega

theorem coarser_part_eq {P Q : Finpartition A} (hPQ : P≤Q)
    {a z : α} (ha : a∈A) (hz : z∈A) (he : P.part a=P.part z) :
    Q.part a=Q.part z := by
  obtain ⟨B,hB,hsub⟩ := hPQ (P.part_mem.mpr ha)
  have haB := hsub (P.mem_part ha)
  have hzB := hsub (he.symm ▸ P.mem_part hz)
  exact (Q.part_eq_of_mem hB haB).trans (Q.part_eq_of_mem hB hzB).symm

def Across (P : Finpartition A) (V : Finset α) : Prop :=
  ∀ a∈V, ∀ z∈V, a≠z → P.part a≠P.part z

theorem across_refinement {P Q : Finpartition A} (hPQ : P≤Q)
    {V : Finset α} (hV : V⊆A) (h : Across Q V) : Across P V := by
  intro a ha z hz hne he
  exact h a ha z hz hne (coarser_part_eq hPQ (hV ha) (hV hz) he)

section Coordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open AnchorCapacity33

def Rank (b : Point ι) : ℕ := ∑ i, b i

omit [DecidableEq ι] in
theorem rank_strict {b c : Point ι} (hle : b≤c) (hne : b≠c) : Rank b<Rank c := by
  apply Finset.sum_lt_sum
  · intro i _; exact hle i
  · have hdiff : ∃ i, b i≠c i := by
      by_contra hh
      apply hne
      funext i
      exact Classical.not_not.mp (fun hi => hh ⟨i,hi⟩)
    obtain ⟨i,hi⟩ := hdiff
    exact ⟨i,Finset.mem_univ i,lt_of_le_of_ne (hle i) hi⟩

def CrossPairs {A : Finset (Point ι)} (P : Finpartition A) : Finset (Point ι × Point ι) :=
  (A×ˢA).filter (fun e => P.part e.1≠P.part e.2)

omit [DecidableEq ι] in
theorem crossPairs_nonempty {A : Finset (Point ι)} (P : Finpartition A)
    (h2 : 2≤P.parts.card) : (CrossPairs P).Nonempty := by
  obtain ⟨B,hB,C,hC,hBC⟩ := Finset.one_lt_card.mp (by omega : 1<P.parts.card)
  obtain ⟨a,ha⟩ := P.nonempty_of_mem_parts hB
  obtain ⟨z,hz⟩ := P.nonempty_of_mem_parts hC
  refine ⟨(a,z),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨P.subset hB ha,P.subset hC hz⟩,?_⟩⟩
  simpa only [P.part_eq_of_mem hB ha,P.part_eq_of_mem hC hz] using hBC

def Selected {A : Finset (Point ι)} (P : Finpartition A) (b : Point ι) :=
  P.parts.filter (fun B => ∃ a∈B, b≤a)

def Representative (b : Point ι) (B : Finset (Point ι)) : Point ι :=
  if h : ∃ a∈B, b≤a then Classical.choose h else b

omit [DecidableEq ι] in
theorem representative_spec {A : Finset (Point ι)} (P : Finpartition A)
    {b : Point ι} {B : Finset (Point ι)} (hB : B∈Selected P b) :
    Representative b B∈B ∧ b≤Representative b B := by
  have hh := (Finset.mem_filter.mp hB).2
  simpa [Representative,hh] using Classical.choose_spec hh

def Representatives {A : Finset (Point ι)} (P : Finpartition A) (b : Point ι) :=
  (Selected P b).image (Representative b)

omit [DecidableEq ι] in
theorem representatives_subset {A : Finset (Point ι)} (P : Finpartition A) (b : Point ι) :
    Representatives P b⊆A := by
  intro a ha
  obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp ha
  exact P.subset (Finset.mem_filter.mp hB).1 (representative_spec P hB).1

omit [DecidableEq ι] in
theorem representatives_injective {A : Finset (Point ι)} (P : Finpartition A) (b : Point ι) :
    Set.InjOn (Representative b) (Selected P b) := by
  intro B hB C hC he
  exact P.eq_of_mem_parts (Finset.mem_filter.mp hB).1 (Finset.mem_filter.mp hC).1
    (representative_spec P hB).1 (he ▸ (representative_spec P hC).1)

omit [DecidableEq ι] in
theorem representatives_card {A : Finset (Point ι)} (P : Finpartition A) (b : Point ι) :
    (Representatives P b).card=(Selected P b).card := by
  exact Finset.card_image_of_injOn (representatives_injective P b)

omit [DecidableEq ι] in
theorem representatives_across {A : Finset (Point ι)} (P : Finpartition A) (b : Point ι) :
    Across P (Representatives P b) := by
  intro a ha z hz hne he
  obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hz
  have hBE := P.part_eq_of_mem (Finset.mem_filter.mp hB).1 (representative_spec P hB).1
  have hCE := P.part_eq_of_mem (Finset.mem_filter.mp hC).1 (representative_spec P hC).1
  have hBC : B=C := hBE.symm.trans (he.trans hCE)
  exact hne (congrArg (Representative b) hBC)

omit [DecidableEq ι] in
theorem selected_contains_above {A : Finset (Point ι)} (P : Finpartition A)
    {b a : Point ι} (ha : a∈A) (hba : b≤a) : P.part a∈Selected P b := by
  exact Finset.mem_filter.mpr ⟨P.part_mem.mpr ha,⟨a,P.mem_part ha,hba⟩⟩

omit [DecidableEq ι] in
theorem maximal_meet_step {A : Finset (Point ι)} (P : Finpartition A)
    (hA : IsAntichain (·≤·) (A : Set (Point ι))) (h2 : 2≤P.parts.card) :
    ∃ b : Point ι,
      2≤(Selected P b).card ∧
      MeetClique b (Representatives P b) ∧
      ∀ a∈A, ∀ z∈A, P.part a≠P.part z → Rank (a⊓z)≤Rank b := by
  obtain ⟨e,he,hmax⟩ := Finset.exists_max_image (CrossPairs P)
    (fun e => Rank (e.1⊓e.2)) (crossPairs_nonempty P h2)
  have he' := Finset.mem_filter.mp he
  have ha := (Finset.mem_product.mp he'.1).1
  have hz := (Finset.mem_product.mp he'.1).2
  let b := e.1⊓e.2
  have hbound : ∀ a∈A, ∀ z∈A, P.part a≠P.part z → Rank (a⊓z)≤Rank b := by
    intro a ha z hz hcross
    exact hmax (a,z) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hz⟩,hcross⟩)
  have hsel2 : 2≤(Selected P b).card := by
    have hsel1 := selected_contains_above P ha (show b≤e.1 from inf_le_left)
    have hsel2 := selected_contains_above P hz (show b≤e.2 from inf_le_right)
    have hh := Finset.one_lt_card.mpr ⟨P.part e.1,hsel1,P.part e.2,hsel2,he'.2⟩
    omega
  have hmeet : ∀ a∈Representatives P b, ∀ z∈Representatives P b, a≠z → a⊓z=b := by
    intro a ha z hz hne
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hz
    have hab := (representative_spec P hB).2
    have hzb := (representative_spec P hC).2
    have hcross := representatives_across P b _ (Finset.mem_image.mpr ⟨B,hB,rfl⟩)
      _ (Finset.mem_image.mpr ⟨C,hC,rfl⟩) hne
    have hm := hbound _ (representatives_subset P b (Finset.mem_image.mpr ⟨B,hB,rfl⟩))
      _ (representatives_subset P b (Finset.mem_image.mpr ⟨C,hC,rfl⟩)) hcross
    have hle : b≤Representative b B⊓Representative b C := le_inf hab hzb
    by_contra hne'
    have hl := rank_strict hle (Ne.symm hne')
    omega
  refine ⟨b,hsel2,⟨?_,hmeet⟩,hbound⟩
  intro a ha
  obtain ⟨B,hB,heq⟩ := Finset.mem_image.mp ha
  refine ⟨heq ▸ (representative_spec P hB).2,?_⟩
  intro hab
  have hv2 : 1<(Representatives P b).card := by rw [representatives_card]; omega
  obtain ⟨z,hz,hza⟩ := Finset.exists_mem_ne hv2 a
  have haz : a≤z := by
    calc a=b := hab
         _=a⊓z := (hmeet a ha z hz hza.symm).symm
         _≤z := inf_le_right
  exact hA (representatives_subset P b ha) (representatives_subset P b hz) hza.symm haz

omit [DecidableEq ι] in
theorem merge_selected_samepart {A : Finset (Point ι)} (P : Finpartition A)
    {b : Point ι} (h2 : 2≤(Selected P b).card)
    {a z : Point ι} (ha : a∈A) (hz : z∈A) (hba : b≤a) (hbz : b≤z) :
    (Merge P (Selected P b) (Finset.filter_subset _ _)
      (Finset.card_pos.mp (by omega))).part a=
    (Merge P (Selected P b) (Finset.filter_subset _ _)
      (Finset.card_pos.mp (by omega))).part z := by
  let Q := Merge P (Selected P b) (Finset.filter_subset _ _)
    (Finset.card_pos.mp (by omega : 0<(Selected P b).card))
  have hU : (Selected P b).biUnion id∈Q.parts := Finset.mem_insert_self _ _
  have haU : a∈(Selected P b).biUnion id :=
    Finset.mem_biUnion.mpr ⟨P.part a,selected_contains_above P ha hba,P.mem_part ha⟩
  have hzU : z∈(Selected P b).biUnion id :=
    Finset.mem_biUnion.mpr ⟨P.part z,selected_contains_above P hz hbz,P.mem_part hz⟩
  exact (Q.part_eq_of_mem hU haU).trans (Q.part_eq_of_mem hU hzU).symm

omit [DecidableEq ι] in
theorem merged_label_unavailable {A : Finset (Point ι)} (P : Finpartition A)
    {b : Point ι} (h2 : 2≤(Selected P b).card)
    {V : Finset (Point ι)} (hV2 : 2≤V.card) (hVA : V⊆A)
    (hc : MeetClique b V) :
    ¬Across (Merge P (Selected P b) (Finset.filter_subset _ _)
      (Finset.card_pos.mp (by omega))) V := by
  intro hcross
  obtain ⟨a,ha,z,hz,hne⟩ := Finset.one_lt_card.mp (by omega : 1<V.card)
  exact hcross a ha z hz hne
    (merge_selected_samepart P h2 (hVA ha) (hVA hz) (hc.1 a ha).1 (hc.1 z hz).1)

def ValidDecomposition {A : Finset (Point ι)} (P : Finpartition A)
    (E : Finset (Point ι × Finset (Point ι))) : Prop :=
  ∀ e∈E, 2≤e.2.card ∧ e.2⊆A ∧ MeetClique e.1 e.2 ∧ Across P e.2

def UniqueLabels (E : Finset (Point ι × Finset (Point ι))) : Prop :=
  ∀ e∈E, ∀ f∈E, e.1=f.1 → e=f

def Fee (E : Finset (Point ι × Finset (Point ι))) : ℕ :=
  ∑ e∈E, (e.2.card-1)

omit [DecidableEq ι] in
theorem partition_collision_decomposition {A : Finset (Point ι)}
    (hA : IsAntichain (·≤·) (A : Set (Point ι))) (P : Finpartition A) :
    ∃ E : Finset (Point ι × Finset (Point ι)),
      ValidDecomposition P E ∧ UniqueLabels E ∧ Fee E=P.parts.card-1 := by
  generalize hn : P.parts.card=n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases h2 : 2≤P.parts.card
    · obtain ⟨b,hsel2,hclique,_⟩ := maximal_meet_step P hA h2
      let C := Selected P b
      have hC : C⊆P.parts := Finset.filter_subset _ _
      have hne : C.Nonempty := Finset.card_pos.mp (by change 0<(Selected P b).card; omega)
      let Q := Merge P C hC hne
      have hQ : Q.parts.card<n := by
        rw [←hn]
        exact merge_strict P hC hsel2
      obtain ⟨E,hvalid,hunique,hfee⟩ := ih Q.parts.card hQ Q rfl
      let e : Point ι × Finset (Point ι) := (b,Representatives P b)
      have hno : ∀ f∈E, f.1≠b := by
        intro f hf heq
        have hf' := hvalid f hf
        have hh : MeetClique b f.2 := heq ▸ hf'.2.2.1
        exact merged_label_unavailable P hsel2 hf'.1 hf'.2.1 hh hf'.2.2.2
      have heE : e∉E := by
        intro hh
        exact hno e hh rfl
      refine ⟨insert e E,?_,?_,?_⟩
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact ⟨by simpa [e,representatives_card] using hsel2,
            representatives_subset P b,hclique,representatives_across P b⟩
        · obtain ⟨hf2,hfA,hfcl,hfcross⟩ := hvalid f hf
          exact ⟨hf2,hfA,hfcl,across_refinement (merge_coarser P hC hne) hfA hfcross⟩
      · intro f hf g hg heq
        rcases Finset.mem_insert.mp hf with rfl | hf
        · rcases Finset.mem_insert.mp hg with rfl | hg
          · rfl
          · exact False.elim (hno g hg heq.symm)
        · rcases Finset.mem_insert.mp hg with rfl | hg
          · exact False.elim (hno f hf heq)
          · exact hunique f hf g hg heq
      · rw [Fee,Finset.sum_insert heE]
        change (Representatives P b).card-1+Fee E=n-1
        rw [←hn,representatives_card,hfee]
        have hcount := merge_card P hC hne
        have hle := Finset.card_le_card hC
        change Q.parts.card=P.parts.card-(Selected P b).card+1 at hcount
        change (Selected P b).card≤P.parts.card at hle
        omega
    · refine ⟨∅,by simp [ValidDecomposition],by simp [UniqueLabels],?_⟩
      simp only [Fee,Finset.sum_empty]
      omega

omit [DecidableEq ι] in
theorem antichain_collision_decomposition {A : Finset (Point ι)}
    (hA : IsAntichain (·≤·) (A : Set (Point ι))) :
    ∃ E : Finset (Point ι × Finset (Point ι)),
      (∀ e∈E, 2≤e.2.card ∧ e.2⊆A ∧ MeetClique e.1 e.2) ∧
      UniqueLabels E ∧ Fee E=A.card-1 := by
  obtain ⟨E,hvalid,hunique,hfee⟩ := partition_collision_decomposition hA (⊥ : Finpartition A)
  refine ⟨E,fun e he => ?_,hunique,?_⟩
  · exact ⟨(hvalid e he).1,(hvalid e he).2.1,(hvalid e he).2.2.1⟩
  · simpa only [Finpartition.card_bot] using hfee

theorem antichain_net_cost_bound (pivot : ι) {A Q : Finset (Point ι)}
    (hA : IsAntichain (·≤·) (A : Set (Point ι))) (hAQ : A⊆Q) :
    A.card-1≤PotentialScore pivot Q := by
  obtain ⟨E,hvalid,hunique,hfee⟩ := antichain_collision_decomposition hA
  have hbound := clique_packing_cost_bound pivot Q E
    (fun e he => ⟨Finset.card_pos.mp (by have hh := (hvalid e he).1; omega),
      (hvalid e he).2.2⟩)
    (fun e he => ((hvalid e he).2.1).trans hAQ)
    (by
      intro e he f hf hne heq
      exact False.elim (hne (hunique e he f hf heq)))
  rw [←hfee]
  exact hbound

theorem antichain_family_net_cost_bound {β : Type*} [DecidableEq β]
    (pivot : ι) (X : Finset β) (owners : β→Finset (Point ι)) (Q : Finset (Point ι))
    (hanti : ∀ x, IsAntichain (·≤·) (owners x : Set (Point ι)))
    (hQ : ∀ x∈X, owners x⊆Q)
    (hcompat : ∀ x∈X, ∀ y∈X, x≠y → ∀ b V W,
      2≤V.card → V⊆owners x → MeetClique b V →
      2≤W.card → W⊆owners y → MeetClique b W → Disjoint V W) :
    (∑ x∈X, ((owners x).card-1))≤PotentialScore pivot Q := by
  let E := fun x => (antichain_collision_decomposition (hanti x)).choose
  have hE := fun x => (antichain_collision_decomposition (hanti x)).choose_spec
  have hdis : (X : Set β).Pairwise (fun x y => Disjoint (E x) (E y)) := by
    intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro e hex hey
    have hxE := (hE x).1 e hex
    have hyE := (hE y).1 e hey
    have hh := hcompat x hx y hy hxy e.1 e.2 e.2
      hxE.1 hxE.2.1 hxE.2.2 hyE.1 hyE.2.1 hyE.2.2
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0<e.2.card)
    exact Finset.disjoint_left.mp hh ha ha
  have hpacking : ∀ e∈X.biUnion E, ∀ f∈X.biUnion E, e≠f → e.1=f.1 → Disjoint e.2 f.2 := by
    intro e he f hf hne heq
    obtain ⟨x,hx,hex⟩ := Finset.mem_biUnion.mp he
    obtain ⟨y,hy,hfy⟩ := Finset.mem_biUnion.mp hf
    by_cases hxy : x=y
    · subst y
      exact False.elim (hne ((hE x).2.1 e hex f hfy heq))
    · have hxE := (hE x).1 e hex
      have hyE := (hE y).1 f hfy
      exact hcompat x hx y hy hxy e.1 e.2 f.2
        hxE.1 hxE.2.1 hxE.2.2 hyE.1 hyE.2.1 (heq.symm ▸ hyE.2.2)
  have hh := clique_packing_cost_bound pivot Q (X.biUnion E)
    (by
      intro e he
      obtain ⟨x,hx,hex⟩ := Finset.mem_biUnion.mp he
      have hxE := (hE x).1 e hex
      exact ⟨Finset.card_pos.mp (by omega),hxE.2.2⟩)
    (by
      intro e he
      obtain ⟨x,hx,hex⟩ := Finset.mem_biUnion.mp he
      exact ((hE x).1 e hex).2.1.trans (hQ x hx)) hpacking
  calc
    (∑ x∈X, ((owners x).card-1))=(∑ x∈X, Fee (E x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (hE x).2.2.symm
    _=(∑ e∈X.biUnion E, (e.2.card-1)) := (Finset.sum_biUnion hdis).symm
    _≤PotentialScore pivot Q := hh

end Coordinates

#print axioms merge_union_nonempty
#print axioms merge_union_not_mem
#print axioms merge_parts_unique
#print axioms merge_parts
#print axioms merge_card
#print axioms merge_coarser
#print axioms merge_fee
#print axioms merge_strict
#print axioms coarser_part_eq
#print axioms across_refinement
#print axioms rank_strict
#print axioms crossPairs_nonempty
#print axioms representative_spec
#print axioms representatives_subset
#print axioms representatives_injective
#print axioms representatives_card
#print axioms representatives_across
#print axioms selected_contains_above
#print axioms maximal_meet_step
#print axioms merge_selected_samepart
#print axioms merged_label_unavailable
#print axioms partition_collision_decomposition
#print axioms antichain_collision_decomposition
#print axioms antichain_net_cost_bound
#print axioms antichain_family_net_cost_bound
end
end JSP233.CollisionTree35
