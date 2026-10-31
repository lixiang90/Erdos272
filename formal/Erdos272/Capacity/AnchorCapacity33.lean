import Erdos272.Foundation.PrimePowerCapacity
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.FinCases

/-! Unbounded actual divisor traces and the pivot-coordinate charging core.
This module does not assume an anchor-capacity inequality. -/
namespace JSP233.AnchorCapacity33
open StarCompletion APGeometry
open scoped Classical BigOperators
noncomputable section

def AnchorTrace (u v d : ℤ) : Finset ℤ :=
  (Finset.Icc u v).filter (fun x => d∣x-u)

def DivisorSteps (S : Finset ℤ) (u v g : ℤ) : Finset ℤ :=
  (Finset.Icc 1 g).filter (fun d => d∣g ∧ AnchorTrace u v d⊆S)

def Retained (D : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  D.filter (fun S => ∀ x∈S, ∃ T∈D, T≠S ∧ x∈T)

theorem mem_anchorTrace (u v d x : ℤ) :
    x∈AnchorTrace u v d ↔ u≤x ∧ x≤v ∧ d∣x-u := by
  simp [AnchorTrace,and_assoc]

theorem mem_divisorSteps (S : Finset ℤ) (u v g d : ℤ) :
    d∈DivisorSteps S u v g ↔ 1≤d ∧ d≤g ∧ d∣g ∧ AnchorTrace u v d⊆S := by
  simp [DivisorSteps,and_assoc]

theorem anchorTrace_antitone {u v d e : ℤ} (hde : d∣e) :
    AnchorTrace u v e⊆AnchorTrace u v d := by
  intro x hx
  obtain ⟨hux,hxv,hex⟩ := (mem_anchorTrace u v e x).mp hx
  exact (mem_anchorTrace u v d x).mpr ⟨hux,hxv,hde.trans hex⟩

theorem anchorTrace_subset_iff {u v g d e : ℤ}
    (hg : 0<g) (hspan : u+g≤v) (hd : 0<d) (hdg : d∣g) :
    AnchorTrace u v d⊆AnchorTrace u v e ↔ e∣d := by
  constructor
  · intro hsub
    have hdle := Int.le_of_dvd hg hdg
    have hmem : u+d∈AnchorTrace u v d :=
      (mem_anchorTrace u v d _).mpr ⟨by omega,by omega,by simp⟩
    simpa using ((mem_anchorTrace u v e _).mp (hsub hmem)).2.2
  · exact anchorTrace_antitone

theorem anchorTrace_eq_iff {u v g d e : ℤ}
    (hg : 0<g) (hspan : u+g≤v) (hd : 0<d) (he : 0<e)
    (hdg : d∣g) (heg : e∣g) :
    AnchorTrace u v d=AnchorTrace u v e ↔ d=e := by
  constructor
  · intro hh
    have hed := (anchorTrace_subset_iff hg hspan hd hdg).mp (fun x hx => hh ▸ hx)
    have hde := (anchorTrace_subset_iff hg hspan he heg).mp (fun x hx => hh.symm ▸ hx)
    exact le_antisymm (Int.le_of_dvd he hde) (Int.le_of_dvd hd hed)
  · rintro rfl; rfl

theorem divisorSteps_upper_closed {S : Finset ℤ} {u v g d e : ℤ}
    (hg : 0<g) (hd : d∈DivisorSteps S u v g)
    (he : 0<e) (heg : e∣g) (hde : d∣e) : e∈DivisorSteps S u v g := by
  obtain ⟨_,_,_,hsub⟩ := (mem_divisorSteps S u v g d).mp hd
  exact (mem_divisorSteps S u v g e).mpr ⟨by omega,Int.le_of_dvd hg heg,heg,
    (anchorTrace_antitone hde).trans hsub⟩

theorem divisorSteps_inter (S T : Finset ℤ) (u v g : ℤ) :
    DivisorSteps (S∩T) u v g=DivisorSteps S u v g∩DivisorSteps T u v g := by
  ext d
  simp only [mem_divisorSteps,Finset.mem_inter]
  constructor
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨⟨h1,h2,h3,fun x hx => (Finset.mem_inter.mp (h4 hx)).1⟩,
      ⟨h1,h2,h3,fun x hx => (Finset.mem_inter.mp (h4 hx)).2⟩⟩
  · rintro ⟨⟨h1,h2,h3,h4⟩,⟨_,_,_,h5⟩⟩
    exact ⟨h1,h2,h3,fun x hx => Finset.mem_inter.mpr ⟨h4 hx,h5 hx⟩⟩

theorem actual_pair_anchor_trace {S T : Finset ℤ} {u v g : ℤ}
    (hpair : IsAP (S∩T)) (hu : u∈S∩T) (hug : u+g∈S∩T) (hv : v∈S∩T) :
    ∃ d : ℤ, 0<d ∧ d∣g ∧ (S∩T)∩Finset.Icc u v=AnchorTrace u v d := by
  obtain ⟨d,p,hAP,_⟩ := (isAP_iff_exists_APAt _).mp hpair
  have hAPu := apAt_rebase hAP hu
  have hdiv := apAt_dvd_sub hAPu hu hug
  refine ⟨d,hAPu.1,by simpa using hdiv,?_⟩
  ext x
  simp only [Finset.mem_inter,Finset.mem_Icc,mem_anchorTrace]
  constructor
  · rintro ⟨hx,hux,hxv⟩
    exact ⟨hux,hxv,apAt_dvd_sub hAPu hu (Finset.mem_inter.mpr hx)⟩
  · rintro ⟨hux,hxv,hdx⟩
    exact ⟨Finset.mem_inter.mp (apAt_fill hAPu hu hv hux hxv hdx),hux,hxv⟩

theorem actual_nonprivate_trace_union {D : Finset (Finset ℤ)}
    {S : Finset ℤ} {u v g : ℤ} (hg : 0<g) (hS : S∈D)
    (hu : ∀ T∈D, u∈T) (hug : ∀ T∈D, u+g∈T) (hv : ∀ T∈D, v∈T)
    (hpair : ∀ T∈D, ∀ R∈D, T≠R → IsAP (T∩R))
    (hcover : ∀ x∈S, ∃ T∈D, T≠S ∧ x∈T) :
    S∩Finset.Icc u v=(DivisorSteps S u v g).biUnion (AnchorTrace u v) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxS,hxI⟩ := Finset.mem_inter.mp hx
    obtain ⟨T,hT,hTS,hxT⟩ := hcover x hxS
    obtain ⟨d,hd,hdg,he⟩ := actual_pair_anchor_trace (hpair S hS T hT hTS.symm)
      (Finset.mem_inter.mpr ⟨hu S hS,hu T hT⟩)
      (Finset.mem_inter.mpr ⟨hug S hS,hug T hT⟩)
      (Finset.mem_inter.mpr ⟨hv S hS,hv T hT⟩)
    have htraceS : AnchorTrace u v d⊆S := by
      rw [←he]
      intro y hy
      exact (Finset.mem_inter.mp (Finset.mem_inter.mp hy).1).1
    exact Finset.mem_biUnion.mpr ⟨d,(mem_divisorSteps S u v g d).mpr
      ⟨by omega,Int.le_of_dvd hg hdg,hdg,htraceS⟩,by
        rw [←he]; exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hxS,hxT⟩,hxI⟩⟩
  · intro hx
    obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
    have hs := ((mem_divisorSteps S u v g d).mp hd).2.2.2 hxd
    have hi := (Finset.mem_filter.mp hxd).1
    exact Finset.mem_inter.mpr ⟨hs,hi⟩

theorem actual_retained_trace_union {D : Finset (Finset ℤ)}
    {S : Finset ℤ} {u v g : ℤ} (hg : 0<g) (hS : S∈Retained D)
    (hu : ∀ T∈D, u∈T) (hug : ∀ T∈D, u+g∈T) (hv : ∀ T∈D, v∈T)
    (hpair : ∀ T∈D, ∀ R∈D, T≠R → IsAP (T∩R)) :
    S∩Finset.Icc u v=(DivisorSteps S u v g).biUnion (AnchorTrace u v) := by
  obtain ⟨hSD,hcover⟩ := Finset.mem_filter.mp hS
  exact actual_nonprivate_trace_union hg hSD hu hug hv hpair hcover

theorem actual_pair_principal_steps {D : Finset (Finset ℤ)}
    {S T : Finset ℤ} {u v g : ℤ} (hg : 0<g) (hspan : u+g≤v)
    (hS : S∈D) (hT : T∈D) (hne : S≠T)
    (hu : ∀ R∈D, u∈R) (hug : ∀ R∈D, u+g∈R) (hv : ∀ R∈D, v∈R)
    (hpair : ∀ R∈D, ∀ U∈D, R≠U → IsAP (R∩U)) :
    ∃ q : ℤ, 0<q ∧ q∣g ∧ ∀ d∈Finset.Icc (1:ℤ) g, d∣g →
      (d∈DivisorSteps S u v g∩DivisorSteps T u v g ↔ q∣d) := by
  obtain ⟨q,hq,hqg,he⟩ := actual_pair_anchor_trace (hpair S hS T hT hne)
    (Finset.mem_inter.mpr ⟨hu S hS,hu T hT⟩)
    (Finset.mem_inter.mpr ⟨hug S hS,hug T hT⟩)
    (Finset.mem_inter.mpr ⟨hv S hS,hv T hT⟩)
  refine ⟨q,hq,hqg,?_⟩
  intro d hd hdg
  have hdpos : 0<d := by have := (Finset.mem_Icc.mp hd).1; omega
  rw [←divisorSteps_inter,mem_divisorSteps]
  have hsub : AnchorTrace u v d⊆S∩T ↔ AnchorTrace u v d⊆AnchorTrace u v q := by
    rw [←he]
    constructor
    · intro hh x hx
      exact Finset.mem_inter.mpr ⟨hh hx,(Finset.mem_filter.mp hx).1⟩
    · intro hh x hx
      exact (Finset.mem_inter.mp (hh hx)).1
  rw [hsub,anchorTrace_subset_iff hg hspan hdpos hdg]
  exact ⟨fun hh => hh.2.2.2,fun hh => ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2,hdg,hh⟩⟩

/-! The universal pivot-coordinate charging lemma. -/
section Charges
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Point (ι : Type*) := ι→ℕ

def PivotBox (pivot : ι) (a : Point ι) : Finset (Point ι) :=
  Fintype.piFinset (fun i => if i=pivot then {a i} else Finset.Iic (a i))

def MeetClique (b : Point ι) (V : Finset (Point ι)) : Prop :=
  (∀ a∈V, b≤a ∧ a≠b) ∧ ∀ a∈V, ∀ z∈V, a≠z → a⊓z=b

theorem mem_pivotBox (pivot : ι) (a b : Point ι) :
    b∈PivotBox pivot a ↔ b≤a ∧ b pivot=a pivot := by
  simp only [PivotBox,Fintype.mem_piFinset]
  constructor
  · intro hh
    refine ⟨fun i => ?_,?_⟩
    · by_cases he : i=pivot
      · subst i; simpa using le_of_eq (Finset.mem_singleton.mp (by simpa using hh pivot))
      · exact Finset.mem_Iic.mp (by simpa [he] using hh i)
    · exact Finset.mem_singleton.mp (by simpa using hh pivot)
  · rintro ⟨hle,heq⟩ i
    by_cases he : i=pivot
    · subst i; simpa using heq
    · simpa [he] using hle i

theorem pivotBox_card (pivot : ι) (a : Point ι) :
    (PivotBox pivot a).card=∏ i∈Finset.univ.erase pivot, (a i+1) := by
  rw [PivotBox,Fintype.card_piFinset]
  have hp := Finset.prod_erase_mul (Finset.univ : Finset ι)
    (fun i => (if i=pivot then {a i} else Finset.Iic (a i)).card) (Finset.mem_univ pivot)
  simp only [if_pos,Finset.card_singleton,mul_one] at hp
  rw [←hp]
  apply Finset.prod_congr rfl
  intro i hi
  have hne : i≠pivot := (Finset.mem_erase.mp hi).1
  simp [hne,Nat.card_Iic]

omit [DecidableEq ι] in
theorem meetClique_root_exists (pivot : ι) {b : Point ι} {V : Finset (Point ι)}
    (hV : V.Nonempty) (hc : MeetClique b V) :
    ∃ r∈V, ∀ a∈V.erase r, a pivot=b pivot := by
  by_cases he : ∃ r∈V, b pivot<r pivot
  · obtain ⟨r,hr,hpr⟩ := he
    refine ⟨r,hr,?_⟩
    intro a ha
    have hne := (Finset.mem_erase.mp ha).1
    have haV := (Finset.mem_erase.mp ha).2
    have hbase := (hc.1 a haV).1 pivot
    have hmeet := congrFun (hc.2 a haV r hr hne) pivot
    change min (a pivot) (r pivot)=b pivot at hmeet
    omega
  · obtain ⟨r,hr⟩ := hV
    refine ⟨r,hr,?_⟩
    intro a ha
    have haV := (Finset.mem_erase.mp ha).2
    have hlo := (hc.1 a haV).1 pivot
    change b pivot≤a pivot at hlo
    have hhi : ¬b pivot<a pivot := fun hh => he ⟨a,haV,hh⟩
    omega

def CliqueRoot (pivot : ι) (b : Point ι) (V : Finset (Point ι)) : Point ι :=
  if h : ∃ r∈V, ∀ a∈V.erase r, a pivot=b pivot then h.choose else 0

theorem cliqueRoot_spec (pivot : ι) {b : Point ι} {V : Finset (Point ι)}
    (hV : V.Nonempty) (hc : MeetClique b V) :
    CliqueRoot pivot b V∈V ∧
      ∀ a∈V.erase (CliqueRoot pivot b V), b∈(PivotBox pivot a).erase a := by
  have hex := meetClique_root_exists pivot hV hc
  have hs : CliqueRoot pivot b V∈V ∧
      ∀ a∈V.erase (CliqueRoot pivot b V), a pivot=b pivot := by
    simpa only [CliqueRoot,dif_pos hex] using hex.choose_spec
  refine ⟨hs.1,?_⟩
  intro a ha
  have hbase := hc.1 a (Finset.mem_erase.mp ha).2
  exact Finset.mem_erase.mpr ⟨Ne.symm hbase.2,
    (mem_pivotBox pivot a b).mpr ⟨hbase.1,(hs.2 a ha).symm⟩⟩

def CliqueCharges (pivot : ι) (entry : Point ι×Finset (Point ι)) :
    Finset (Point ι×Point ι) :=
  (entry.2.erase (CliqueRoot pivot entry.1 entry.2)).image (fun a => (a,entry.1))

def PotentialCharges (pivot : ι) (Q : Finset (Point ι)) : Finset (Point ι×Point ι) :=
  Q.biUnion (fun a => ((PivotBox pivot a).erase a).image (fun b => (a,b)))

def PotentialScore (pivot : ι) (Q : Finset (Point ι)) : ℕ :=
  ∑ a∈Q, ((∏ i∈Finset.univ.erase pivot, (a i+1))-1)

theorem cliqueCharges_card (pivot : ι) {entry : Point ι×Finset (Point ι)}
    (hV : entry.2.Nonempty) (hc : MeetClique entry.1 entry.2) :
    (CliqueCharges pivot entry).card=entry.2.card-1 := by
  rw [CliqueCharges,Finset.card_image_of_injective]
  · exact Finset.card_erase_of_mem (cliqueRoot_spec pivot hV hc).1
  · intro a b he
    exact congrArg Prod.fst he

theorem potentialCharges_card (pivot : ι) (Q : Finset (Point ι)) :
    (PotentialCharges pivot Q).card=PotentialScore pivot Q := by
  rw [PotentialCharges,Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.card_image_of_injective]
    · have haBox : a∈PivotBox pivot a := (mem_pivotBox pivot a a).mpr ⟨le_rfl,rfl⟩
      rw [Finset.card_erase_of_mem haBox,pivotBox_card]
    · intro b c he
      exact congrArg Prod.snd he
  · intro a ha b hb hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨x,hx,hxp⟩ := Finset.mem_image.mp hp
    obtain ⟨y,hy,hyp⟩ := Finset.mem_image.mp hq
    exact hne (congrArg Prod.fst (hxp.trans hyp.symm))

omit [DecidableEq ι] in
theorem cliqueCharges_pairwise (pivot : ι) (P : Finset (Point ι×Finset (Point ι)))
    (hpack : ∀ e∈P, ∀ f∈P, e≠f → e.1=f.1 → Disjoint e.2 f.2) :
    (P : Set (Point ι×Finset (Point ι))).PairwiseDisjoint (CliqueCharges pivot) := by
  intro e he f hf hne
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨a,ha,hap⟩ := Finset.mem_image.mp hp
  obtain ⟨b,hb,hbp⟩ := Finset.mem_image.mp hq
  have hab : a=b := congrArg Prod.fst (hap.trans hbp.symm)
  have hef : e.1=f.1 := congrArg Prod.snd (hap.trans hbp.symm)
  exact Finset.disjoint_left.mp (hpack e he f hf hne hef)
    (Finset.mem_erase.mp ha).2 (hab ▸ (Finset.mem_erase.mp hb).2)

theorem clique_packing_cost_bound (pivot : ι) (Q : Finset (Point ι))
    (P : Finset (Point ι×Finset (Point ι)))
    (hclique : ∀ e∈P, e.2.Nonempty ∧ MeetClique e.1 e.2)
    (hvertices : ∀ e∈P, e.2⊆Q)
    (hpack : ∀ e∈P, ∀ f∈P, e≠f → e.1=f.1 → Disjoint e.2 f.2) :
    (∑ e∈P, (e.2.card-1))≤PotentialScore pivot Q := by
  have hsub : P.biUnion (CliqueCharges pivot)⊆PotentialCharges pivot Q := by
    intro p hp
    obtain ⟨e,he,hpe⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hpe
    have hca := (cliqueRoot_spec pivot (hclique e he).1 (hclique e he).2).2 a ha
    exact Finset.mem_biUnion.mpr ⟨a,hvertices e he (Finset.mem_erase.mp ha).2,
      Finset.mem_image.mpr ⟨e.1,hca,rfl⟩⟩
  calc
    (∑ e∈P, (e.2.card-1))=(P.biUnion (CliqueCharges pivot)).card := by
      rw [Finset.card_biUnion (cliqueCharges_pairwise pivot P hpack)]
      apply Finset.sum_congr rfl
      intro e he
      exact (cliqueCharges_card pivot (hclique e he).1 (hclique e he).2).symm
    _≤(PotentialCharges pivot Q).card := Finset.card_le_card hsub
    _=PotentialScore pivot Q := potentialCharges_card pivot Q

/-! The common-key obstruction used by the first nonprincipal-prefix map. -/
def JoinClosed (Q : Finset (Point ι)) : Prop :=
  ∀ a∈Q, ∀ b∈Q, a⊔b∈Q

def PrefixWitness (j : ι) (Q : Finset (Point ι)) (top : Point ι) (i : ι) : Prop :=
  i≠j ∧ top∈Q ∧ Function.update (Function.update top i (top i+1)) j 0∈Q ∧
    Function.update top i (top i+1)∉Q

theorem principal_joinClosed (a : Point ι) : JoinClosed (Finset.Iic a) := by
  intro x hx y hy
  exact Finset.mem_Iic.mpr (sup_le (Finset.mem_Iic.mp hx) (Finset.mem_Iic.mp hy))

omit [Fintype ι] in
theorem prefix_witness_join (j i : ι) (top : Point ι) (hij : i≠j) :
    top⊔Function.update (Function.update top i (top i+1)) j 0=
      Function.update top i (top i+1) := by
  funext k
  by_cases hki : k=i
  · subst k
    simp [Function.update,hij]
  · by_cases hkj : k=j
    · subst k
      simp [Function.update,hij.symm]
    · simp [Function.update,hki,hkj]

theorem prefix_same_key_impossible {j i : ι} {Q R : Finset (Point ι)} {top : Point ι}
    (hQR : JoinClosed (Q∩R)) (hQ : PrefixWitness j Q top i)
    (hR : PrefixWitness j R top i) : False := by
  have hjoin := hQR top (Finset.mem_inter.mpr ⟨hQ.2.1,hR.2.1⟩)
    _ (Finset.mem_inter.mpr ⟨hQ.2.2.1,hR.2.2.1⟩)
  rw [prefix_witness_join j i top hQ.1] at hjoin
  exact hQ.2.2.2 (Finset.mem_inter.mp hjoin).1

theorem prefix_keys_injective (j : ι) (F : Finset (Finset (Point ι)))
    (key : Finset (Point ι)→Point ι×ι)
    (hpair : ∀ Q∈F, ∀ R∈F, Q≠R → JoinClosed (Q∩R))
    (hkey : ∀ Q∈F, PrefixWitness j Q (key Q).1 (key Q).2) :
    Set.InjOn key (F : Set (Finset (Point ι))) := by
  intro Q hQ R hR he
  by_contra hne
  have hRkey : PrefixWitness j R (key Q).1 (key Q).2 := by rw [he]; exact hkey R hR
  exact prefix_same_key_impossible (hpair Q hQ R hR hne) (hkey Q hQ) hRkey

theorem prefix_family_card_bound (j : ι) (Q : Finset (Point ι))
    (F : Finset (Finset (Point ι))) (key : Finset (Point ι)→Point ι×ι)
    (hsub : ∀ R∈F, R⊆Q)
    (hpair : ∀ R∈F, ∀ S∈F, R≠S → JoinClosed (R∩S))
    (hkey : ∀ R∈F, PrefixWitness j R (key R).1 (key R).2) :
    F.card≤Q.card*(Fintype.card ι-1) := by
  have hmap : F.image key⊆Q.product ((Finset.univ : Finset ι).erase j) := by
    intro p hp
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨hsub R hR (hkey R hR).2.1,
      Finset.mem_erase.mpr ⟨(hkey R hR).1,Finset.mem_univ _⟩⟩
  have hh := Finset.card_le_card hmap
  rw [Finset.card_image_of_injOn (prefix_keys_injective j F key hpair hkey)] at hh
  simpa using hh

def DownClosed (Q : Finset (Point ι)) : Prop :=
  ∀ a∈Q, ∀ b, b≤a → b∈Q

theorem downclosed_face_bounds {j : ι} {Q : Finset (Point ι)} {a : Point ι}
    (hdown : DownClosed Q) (hface : Q.filter (fun x => x j=0)=Finset.Iic a)
    {x : Point ι} (hx : x∈Q) : Function.update x j 0≤a := by
  have hflat : Function.update x j 0∈Q := hdown x hx _ (by
    intro i
    by_cases hi : i=j
    · subst i; simp
    · simp [hi])
  have hh : Function.update x j 0∈Q.filter (fun x => x j=0) :=
    Finset.mem_filter.mpr ⟨hflat,by simp⟩
  rw [hface] at hh
  exact Finset.mem_Iic.mp hh

theorem prefix_witness_exists (j : ι) (Q : Finset (Point ι)) (a : Point ι)
    (hdown : DownClosed Q) (hface : Q.filter (fun x => x j=0)=Finset.Iic a)
    (hnonprincipal : ¬∃ b : Point ι, Q=Finset.Iic b) :
    ∃ top : Point ι, ∃ i : ι, 0<top j ∧ PrefixWitness j Q top i := by
  have haFace : a∈Q.filter (fun x => x j=0) := by
    rw [hface]; exact Finset.mem_Iic.mpr le_rfl
  have haQ := (Finset.mem_filter.mp haFace).1
  have haj := (Finset.mem_filter.mp haFace).2
  obtain ⟨z,hzQ,hmax⟩ := Finset.exists_max_image Q (fun x => x j) ⟨a,haQ⟩
  let level := z j
  let layer := Q.filter (fun x => x j=level)
  have hLayer : layer.Nonempty := ⟨z,Finset.mem_filter.mpr ⟨hzQ,rfl⟩⟩
  obtain ⟨top,htop,hmaximal⟩ := layer.exists_maximal hLayer
  have htopQ := (Finset.mem_filter.mp htop).1
  have htopLevel := (Finset.mem_filter.mp htop).2
  let corner := Function.update a j level
  have hQbound : ∀ x∈Q, x≤corner := by
    intro x hx k
    by_cases hkj : k=j
    · subst k
      simpa only [corner,Function.update_self] using hmax x hx
    · have hh := downclosed_face_bounds hdown hface hx k
      simpa only [Function.update_of_ne hkj,corner] using hh
  have hcorner : corner∉Q := by
    intro hc
    apply hnonprincipal
    refine ⟨corner,Finset.Subset.antisymm (fun x hx => Finset.mem_Iic.mpr (hQbound x hx)) ?_⟩
    intro x hx
    exact hdown corner hc x (Finset.mem_Iic.mp hx)
  have hlevel : 0<level := by
    by_contra hn
    have hl0 : level=0 := by omega
    have he : corner=a := by simp [corner,hl0,Function.update_eq_self_iff,haj]
    exact hcorner (he.symm ▸ haQ)
  have htopCorner : top≠corner := by intro he; exact hcorner (he ▸ htopQ)
  have hex : ∃ i : ι, i≠j ∧ top i<a i := by
    by_contra hn
    apply htopCorner
    funext k
    by_cases hkj : k=j
    · subst k; simpa only [corner,Function.update_self] using htopLevel
    · have hlo := hQbound top htopQ k
      have hhi : ¬top k<a k := fun hlt => hn ⟨k,hkj,hlt⟩
      have hk : corner k=a k := by simp only [corner,Function.update_of_ne hkj]
      rw [hk] at hlo
      rw [hk]
      exact le_antisymm hlo (by omega)
  obtain ⟨i,hij,hi⟩ := hex
  let inc := Function.update top i (top i+1)
  have hflatInc : Function.update inc j 0∈Q := by
    have hle : Function.update inc j 0≤a := by
      intro k
      by_cases hkj : k=j
      · subst k; simp [haj]
      · by_cases hki : k=i
        · subst k; simp only [Function.update_of_ne hij,inc,Function.update_self]; omega
        · have hh := downclosed_face_bounds hdown hface htopQ k
          simpa only [inc,Function.update_of_ne hkj,Function.update_of_ne hki] using hh
    have hh : Function.update inc j 0∈Q.filter (fun x => x j=0) := by
      rw [hface]; exact Finset.mem_Iic.mpr hle
    exact (Finset.mem_filter.mp hh).1
  have hinc : inc∉Q := by
    intro hiQ
    have hiLayer : inc∈layer := Finset.mem_filter.mpr ⟨hiQ,by
      simpa only [inc,Function.update_of_ne hij.symm] using htopLevel⟩
    have htopInc : top≤inc := by
      intro k
      by_cases hki : k=i
      · subst k; simp [inc]
      · simp [inc,hki]
    have hh := hmaximal hiLayer htopInc i
    simp only [inc,Function.update_self] at hh
    omega
  exact ⟨top,i,by omega,hij,htopQ,hflatInc,hinc⟩

theorem nonprincipal_prefix_family_card_bound (j : ι) (Q : Finset (Point ι))
    (F : Finset (Finset (Point ι))) (hsub : ∀ R∈F, R⊆Q)
    (hpair : ∀ R∈F, ∀ S∈F, R≠S → JoinClosed (R∩S))
    (hdown : ∀ R∈F, DownClosed R)
    (hface : ∀ R∈F, ∃ a : Point ι, R.filter (fun x => x j=0)=Finset.Iic a)
    (hnonprincipal : ∀ R∈F, ¬∃ b : Point ι, R=Finset.Iic b) :
    F.card≤(Q.filter (fun x => 0<x j)).card*(Fintype.card ι-1) := by
  have hex : ∀ R∈F, ∃ p : Point ι×ι,
      0<p.1 j ∧ PrefixWitness j R p.1 p.2 := by
    intro R hR
    obtain ⟨a,ha⟩ := hface R hR
    obtain ⟨top,i,hpos,hw⟩ := prefix_witness_exists j R a (hdown R hR) ha (hnonprincipal R hR)
    exact ⟨(top,i),hpos,hw⟩
  let key := fun R => if hr : R∈F then (hex R hr).choose else (0,j)
  have hkey : ∀ R∈F, 0<(key R).1 j ∧ PrefixWitness j R (key R).1 (key R).2 := by
    intro R hR
    simpa only [key,dif_pos hR] using (hex R hR).choose_spec
  have hmap : F.image key⊆(Q.filter (fun x => 0<x j)).product
      ((Finset.univ : Finset ι).erase j) := by
    intro p hp
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
      ⟨hsub R hR (hkey R hR).2.2.1,(hkey R hR).1⟩,
      Finset.mem_erase.mpr ⟨(hkey R hR).2.1,Finset.mem_univ _⟩⟩
  have hh := Finset.card_le_card hmap
  rw [Finset.card_image_of_injOn (prefix_keys_injective j F key hpair (fun R hR => (hkey R hR).2))] at hh
  simpa using hh

def Hull (Q : Finset (Point ι)) : Point ι := fun i => Q.sup (fun x => x i)

def AxisPoint (i : ι) (n : ℕ) : Point ι := Function.update 0 i n

omit [Fintype ι] [DecidableEq ι] in
theorem point_le_hull {Q : Finset (Point ι)} {x : Point ι} (hx : x∈Q) : x≤Hull Q := by
  intro i
  exact Finset.le_sup (f:=fun y : Point ι => y i) hx

theorem hull_not_mem {Q : Finset (Point ι)} (hdown : DownClosed Q)
    (hnonprincipal : ¬∃ a : Point ι, Q=Finset.Iic a) : Hull Q∉Q := by
  intro hmem
  apply hnonprincipal
  exact ⟨Hull Q,Finset.Subset.antisymm
    (fun x hx => Finset.mem_Iic.mpr (point_le_hull hx))
    (fun x hx => hdown _ hmem x (Finset.mem_Iic.mp hx))⟩

omit [Fintype ι] in
theorem axisPoint_mem {Q : Finset (Point ι)} (hQ : Q.Nonempty)
    (hdown : DownClosed Q) (i : ι) : AxisPoint i (Hull Q i)∈Q := by
  obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup Q hQ (fun x => x i)
  apply hdown x hx
  intro k
  by_cases hki : k=i
  · subst k
    simpa only [AxisPoint,Function.update_self,Hull] using le_of_eq he
  · simp [AxisPoint,hki]

def Projection (I : Finset ι) (a : Point ι) : Point ι :=
  fun i => if i∈I then a i else 0

def Face (I : Finset ι) (Q : Finset (Point ι)) : Finset (Point ι) :=
  Q.filter (fun x => ∀ i, i∉I → x i=0)

omit [Fintype ι] in
theorem projection_le (I : Finset ι) (a : Point ι) : Projection I a≤a := by
  intro i
  by_cases hi : i∈I <;> simp [Projection,hi]

omit [Fintype ι] in
theorem projection_mem {I : Finset ι} {Q : Finset (Point ι)}
    (hdown : DownClosed Q) {a : Point ι} (ha : a∈Q) : Projection I a∈Q :=
  hdown a ha _ (projection_le I a)

theorem face_eq_projection_image (I : Finset ι) (Q : Finset (Point ι))
    (hdown : DownClosed Q) : Face I Q=Q.image (Projection I) := by
  ext a
  constructor
  · intro ha
    obtain ⟨haQ,haI⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_image.mpr ⟨a,haQ,by
      funext i; by_cases hi : i∈I <;> simp [Projection,hi,haI i]⟩
  · intro ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_filter.mpr ⟨projection_mem hdown hb,by
      intro i hi; simp [Projection,hi]⟩

theorem face_inter (I : Finset ι) (Q R : Finset (Point ι)) :
    Face I (Q∩R)=Face I Q∩Face I R := by
  ext a
  simp only [Face,Finset.mem_filter,Finset.mem_inter]
  tauto

theorem face_downclosed (I : Finset ι) {Q : Finset (Point ι)} (hdown : DownClosed Q) :
    DownClosed (Face I Q) := by
  intro a ha b hba
  obtain ⟨haQ,haI⟩ := Finset.mem_filter.mp ha
  refine Finset.mem_filter.mpr ⟨hdown a haQ b hba,?_⟩
  intro i hi
  have hh : b i≤a i := hba i
  rw [haI i hi] at hh
  omega

theorem face_principal (I : Finset ι) (a : Point ι) :
    Face I (Finset.Iic a)=Finset.Iic (Projection I a) := by
  ext b
  simp only [Face,Finset.mem_filter,Finset.mem_Iic]
  constructor
  · rintro ⟨hba,hout⟩ i
    by_cases hi : i∈I
    · simpa [Projection,hi] using hba i
    · simp [Projection,hi,hout i hi]
  · intro hb
    refine ⟨le_trans hb (projection_le I a),?_⟩
    intro i hi
    have hh := hb i
    simp only [Projection,if_neg hi] at hh
    omega

theorem downclosed_projection_inter (I : Finset ι) (Q R : Finset (Point ι))
    (hQ : DownClosed Q) (hR : DownClosed R) :
    (Q∩R).image (Projection I)=Q.image (Projection I)∩R.image (Projection I) := by
  have hQR : DownClosed (Q∩R) := by
    intro a ha b hba
    exact Finset.mem_inter.mpr ⟨hQ a (Finset.mem_inter.mp ha).1 b hba,
      hR a (Finset.mem_inter.mp ha).2 b hba⟩
  rw [←face_eq_projection_image I (Q∩R) hQR,
    ←face_eq_projection_image I Q hQ,←face_eq_projection_image I R hR,face_inter]

theorem nonprincipal_prefix_family_card_bound_on (j : ι) (I : Finset ι)
    (Q : Finset (Point ι)) (F : Finset (Finset (Point ι))) (hjI : j∈I)
    (hsupport : ∀ x∈Q, ∀ i, i∉I → x i=0)
    (hsub : ∀ R∈F, R⊆Q)
    (hpair : ∀ R∈F, ∀ S∈F, R≠S → JoinClosed (R∩S))
    (hdown : ∀ R∈F, DownClosed R)
    (hface : ∀ R∈F, ∃ a : Point ι, R.filter (fun x => x j=0)=Finset.Iic a)
    (hnonprincipal : ∀ R∈F, ¬∃ b : Point ι, R=Finset.Iic b) :
    F.card≤(Q.filter (fun x => 0<x j)).card*(I.card-1) := by
  have hex : ∀ R∈F, ∃ p : Point ι×ι,
      0<p.1 j ∧ PrefixWitness j R p.1 p.2 := by
    intro R hR
    obtain ⟨a,ha⟩ := hface R hR
    obtain ⟨top,i,hpos,hw⟩ := prefix_witness_exists j R a (hdown R hR) ha (hnonprincipal R hR)
    exact ⟨(top,i),hpos,hw⟩
  let key := fun R => if hr : R∈F then (hex R hr).choose else (0,j)
  have hkey : ∀ R∈F, 0<(key R).1 j ∧ PrefixWitness j R (key R).1 (key R).2 := by
    intro R hR
    simpa only [key,dif_pos hR] using (hex R hR).choose_spec
  have hmap : F.image key⊆(Q.filter (fun x => 0<x j)).product (I.erase j) := by
    intro p hp
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hp
    have hwi := (hkey R hR).2.1
    have hiI : (key R).2∈I := by
      by_contra hn
      have hx := hsub R hR (hkey R hR).2.2.2.1
      have hh := hsupport _ hx (key R).2 hn
      simp only [Function.update_of_ne hwi,Function.update_self] at hh
      omega
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
      ⟨hsub R hR (hkey R hR).2.2.1,(hkey R hR).1⟩,
      Finset.mem_erase.mpr ⟨hwi,hiI⟩⟩
  have hh := Finset.card_le_card hmap
  rw [Finset.card_image_of_injOn (prefix_keys_injective j F key hpair (fun R hR => (hkey R hR).2))] at hh
  simpa [Finset.card_erase_of_mem hjI] using hh

theorem downclosed_joinClosed_principal {Q : Finset (Point ι)} (hQ : Q.Nonempty)
    (hdown : DownClosed Q) (hjoin : JoinClosed Q) :
    ∃ a : Point ι, Q=Finset.Iic a := by
  obtain ⟨a,ha,hmax⟩ := Q.exists_maximal hQ
  refine ⟨a,Finset.Subset.antisymm ?_ ?_⟩
  · intro x hx
    have hh : a⊔x≤a := hmax (hjoin a ha x hx) le_sup_left
    exact Finset.mem_Iic.mpr (le_trans le_sup_right hh)
  · intro x hx
    exact hdown a ha x (Finset.mem_Iic.mp hx)

theorem nonprincipal_trace_image_injective {α : Type*} (D : Finset α)
    (trace : α→Finset (Point ι))
    (hne : ∀ S∈D, (trace S).Nonempty)
    (hdown : ∀ S∈D, DownClosed (trace S))
    (hnonprincipal : ∀ S∈D, ¬∃ a : Point ι, trace S=Finset.Iic a)
    (hpair : ∀ S∈D, ∀ T∈D, S≠T → JoinClosed (trace S∩trace T)) :
    Set.InjOn trace (D : Set α) := by
  intro S hS T hT he
  by_contra hST
  have hj := hpair S hS T hT hST
  rw [←he,Finset.inter_self] at hj
  exact hnonprincipal S hS (downclosed_joinClosed_principal (hne S hS) (hdown S hS) hj)

end Charges

theorem two_axis_join (a : Point (Fin 2)) :
    AxisPoint (0:Fin 2) (a 0)⊔AxisPoint (1:Fin 2) (a 1)=a := by
  funext i
  fin_cases i <;> simp [AxisPoint]

theorem two_hull_first_pos {Q : Finset (Point (Fin 2))} (hQ : Q.Nonempty)
    (hdown : DownClosed Q) (hnonprincipal : ¬∃ a : Point (Fin 2), Q=Finset.Iic a) :
    0<Hull Q 0 := by
  by_contra hn
  have hz : Hull Q 0=0 := by omega
  have he : AxisPoint (1:Fin 2) (Hull Q 1)=Hull Q := by
    funext i
    fin_cases i <;> simp [AxisPoint,hz]
  exact hull_not_mem hdown hnonprincipal (he ▸ axisPoint_mem hQ hdown (1:Fin 2))

theorem two_hull_comparable_impossible {Q R : Finset (Point (Fin 2))}
    (hQ : Q.Nonempty) (hR : R.Nonempty) (hdQ : DownClosed Q) (hdR : DownClosed R)
    (hnQ : ¬∃ a : Point (Fin 2), Q=Finset.Iic a)
    (hjoin : JoinClosed (Q∩R)) (hle : Hull Q≤Hull R) : False := by
  have haxis : ∀ i : Fin 2, AxisPoint i (Hull Q i)∈Q∩R := by
    intro i
    refine Finset.mem_inter.mpr ⟨axisPoint_mem hQ hdQ i,?_⟩
    apply hdR _ (axisPoint_mem hR hdR i)
    intro k
    by_cases hki : k=i
    · subst k; simpa only [AxisPoint,Function.update_self] using hle i
    · simp [AxisPoint,hki]
  have hj := hjoin _ (haxis 0) _ (haxis 1)
  rw [two_axis_join] at hj
  exact hull_not_mem hdQ hnQ (Finset.mem_inter.mp hj).1

theorem two_hull_first_injective (F : Finset (Finset (Point (Fin 2))))
    (hQ : ∀ Q∈F, Q.Nonempty) (hdown : ∀ Q∈F, DownClosed Q)
    (hnonprincipal : ∀ Q∈F, ¬∃ a : Point (Fin 2), Q=Finset.Iic a)
    (hpair : ∀ Q∈F, ∀ R∈F, Q≠R → JoinClosed (Q∩R)) :
    Set.InjOn (fun Q => Hull Q (0:Fin 2)) (F : Set (Finset (Point (Fin 2)))) := by
  intro Q hQF R hRF he
  by_contra hne
  rcases le_total (Hull Q 1) (Hull R 1) with hle | hle
  · apply two_hull_comparable_impossible (hQ Q hQF) (hQ R hRF) (hdown Q hQF) (hdown R hRF)
      (hnonprincipal Q hQF) (hpair Q hQF R hRF hne)
    intro i
    fin_cases i
    · exact le_of_eq he
    · exact hle
  · apply two_hull_comparable_impossible (hQ R hRF) (hQ Q hQF) (hdown R hRF) (hdown Q hQF)
      (hnonprincipal R hRF) (hpair R hRF Q hQF (Ne.symm hne))
    intro i
    fin_cases i
    · exact le_of_eq he.symm
    · exact hle

theorem two_nonprincipal_family_card_bound (F : Finset (Finset (Point (Fin 2)))) (n : ℕ)
    (hQ : ∀ Q∈F, Q.Nonempty) (hdown : ∀ Q∈F, DownClosed Q)
    (hnonprincipal : ∀ Q∈F, ¬∃ a : Point (Fin 2), Q=Finset.Iic a)
    (hpair : ∀ Q∈F, ∀ R∈F, Q≠R → JoinClosed (Q∩R))
    (hbound : ∀ Q∈F, ∀ x∈Q, x (0:Fin 2)≤n) : F.card≤n := by
  have hsub : F.image (fun Q => Hull Q (0:Fin 2))⊆Finset.Icc 1 n := by
    intro z hz
    obtain ⟨Q,hQF,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_Icc.mpr ⟨two_hull_first_pos (hQ Q hQF) (hdown Q hQF) (hnonprincipal Q hQF),
      Finset.sup_le (hbound Q hQF)⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (two_hull_first_injective F hQ hdown hnonprincipal hpair)] at hh
  simpa using hh

#print axioms mem_anchorTrace
#print axioms mem_divisorSteps
#print axioms anchorTrace_antitone
#print axioms anchorTrace_subset_iff
#print axioms anchorTrace_eq_iff
#print axioms divisorSteps_upper_closed
#print axioms divisorSteps_inter
#print axioms actual_pair_anchor_trace
#print axioms actual_nonprivate_trace_union
#print axioms actual_retained_trace_union
#print axioms actual_pair_principal_steps
#print axioms mem_pivotBox
#print axioms pivotBox_card
#print axioms meetClique_root_exists
#print axioms cliqueRoot_spec
#print axioms cliqueCharges_card
#print axioms potentialCharges_card
#print axioms cliqueCharges_pairwise
#print axioms clique_packing_cost_bound
#print axioms principal_joinClosed
#print axioms prefix_witness_join
#print axioms prefix_same_key_impossible
#print axioms prefix_keys_injective
#print axioms prefix_family_card_bound
#print axioms downclosed_face_bounds
#print axioms prefix_witness_exists
#print axioms nonprincipal_prefix_family_card_bound
#print axioms point_le_hull
#print axioms hull_not_mem
#print axioms axisPoint_mem
#print axioms projection_le
#print axioms projection_mem
#print axioms face_eq_projection_image
#print axioms face_inter
#print axioms face_downclosed
#print axioms face_principal
#print axioms downclosed_projection_inter
#print axioms nonprincipal_prefix_family_card_bound_on
#print axioms downclosed_joinClosed_principal
#print axioms nonprincipal_trace_image_injective
#print axioms two_axis_join
#print axioms two_hull_first_pos
#print axioms two_hull_comparable_impossible
#print axioms two_hull_first_injective
#print axioms two_nonprincipal_family_card_bound
end
end JSP233.AnchorCapacity33
