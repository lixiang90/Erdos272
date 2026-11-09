module

public import Erdos272.Counting.WitnessInterval43
public import Erdos272.Resources.ExteriorWitness36
public import Erdos272.Geometry.Reflect37
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Actual restricted bad witnesses: no witness at the selected anchor gives
AP covers, and crooked traces give private two-divisor codes. -/
namespace JSP233.RestrictedWitness44
open StarCompletion LongTerminal35 WitnessInterval43 APGeometry
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000

def Distance (c p : ℤ) : ℕ := (p-c).natAbs
def Trace (S : Finset ℤ) (c p : ℤ) : Finset ℤ :=
  S∩Finset.Icc (min c p) (max c p)
def Segment (c p : ℤ) (d : ℕ) : Finset ℤ :=
  (Finset.Icc (min c p) (max c p)).filter (fun x => (d:ℤ)∣x-c)
def Cover (S U : Finset ℤ) : Prop := ∃ A,IsAP A ∧ U⊆A ∧ A⊆S
def AllCovered (S : Finset ℤ) (c p : ℤ) : Prop :=
  ∀ x∈S,Cover S {c,p,x}
def IncompatibleCode (S : Finset ℤ) (c p : ℤ) (d e : ℕ) : Prop :=
  Segment c p d⊆S ∧ Segment c p e⊆S ∧ ¬Cover S (Segment c p d∪Segment c p e)
def BadMembers (F : Finset (Finset ℤ)) (c : ℤ) (P : Finset ℤ) : Finset (Finset ℤ) :=
  F.filter (fun S => c∈S ∧ ¬IsAP S ∧ (S.erase c∩P).Nonempty ∧
    ∀ Q,IntrinsicPair c S Q → Disjoint Q P)
def Anchor (S : Finset ℤ) (c : ℤ) (P : Finset ℤ) : ℤ :=
  if h:(S.erase c∩P).Nonempty then (S.erase c∩P).min' h else c
def CrookedTraceBad (F : Finset (Finset ℤ)) (c : ℤ) (P : Finset ℤ) : Finset (Finset ℤ) :=
  (BadMembers F c P).filter (fun S => ¬IsAP (Trace S c (Anchor S c P)))
def APTraceBad (F : Finset (Finset ℤ)) (c : ℤ) (P : Finset ℤ) : Finset (Finset ℤ) :=
  (BadMembers F c P).filter (fun S => IsAP (Trace S c (Anchor S c P)))

theorem all_covered_of_no_witness_at {S : Finset ℤ} {c p : ℤ}
    (hc : c∈S) (hp : p∈S) (hpc : p≠c)
    (hno : ∀ x,¬IntrinsicPair c S {p,x}) : AllCovered S c p := by
  intro x hx
  by_cases hxc : x=c
  · subst x
    refine ⟨{c,p},pair_isAP c p,?_,?_⟩
    · intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz ⊢
      aesop
    · exact Finset.insert_subset_iff.mpr ⟨hc,Finset.singleton_subset_iff.mpr hp⟩
  by_cases hxp : x=p
  · subst x
    refine ⟨{c,p},pair_isAP c p,by simp,Finset.insert_subset_iff.mpr ⟨hc,Finset.singleton_subset_iff.mpr hp⟩⟩
  by_contra hn
  apply hno x
  refine ⟨by simp [Ne.symm hxp],by simp [Ne.symm hpc,Ne.symm hxc],?_,?_⟩
  · exact Finset.insert_subset_iff.mpr ⟨hp,Finset.singleton_subset_iff.mpr hx⟩
  · exact hn

theorem intrinsic_trace_lift {S Q : Finset ℤ} {c p : ℤ}
    (hQ : IntrinsicPair c (Trace S c p) Q) : IntrinsicPair c S Q := by
  refine ⟨hQ.1,hQ.2.1,(hQ.2.2.1.trans Finset.inter_subset_left),?_⟩
  rintro ⟨A,hAP,hCA,hAS⟩
  have hcI : c∈Finset.Icc (min c p) (max c p) := Finset.mem_Icc.mpr ⟨min_le_left _ _,le_max_left _ _⟩
  have hcA := hCA (Finset.mem_insert_self c Q)
  have hclip : IsAP (A∩Finset.Icc (min c p) (max c p)) :=
    isAP_inter_of_nonempty hAP (integer_interval_isAP _ _ min_le_max)
      ⟨c,Finset.mem_inter.mpr ⟨hcA,hcI⟩⟩
  apply hQ.2.2.2
  refine ⟨A∩Finset.Icc (min c p) (max c p),hclip,?_,?_⟩
  · intro x hx
    refine Finset.mem_inter.mpr ⟨hCA hx,?_⟩
    rcases Finset.mem_insert.mp hx with rfl|hxQ
    · exact hcI
    · exact (Finset.mem_inter.mp (hQ.2.2.1 hxQ)).2
  · intro x hx
    exact Finset.mem_inter.mpr ⟨hAS (Finset.mem_inter.mp hx).1,(Finset.mem_inter.mp hx).2⟩

theorem actual_AP_trace_segment {A : Finset ℤ} {c p : ℤ}
    (hAP : IsAP A) (hc : c∈A) (hp : p∈A) :
    ∃ d:ℕ,0<d ∧ d∣Distance c p ∧
      A∩Finset.Icc (min c p) (max c p)=Segment c p d := by
  obtain ⟨e,b,hA,_⟩ := (isAP_iff_exists_APAt A).mp hAP
  have he := hA.1
  have hdcast : (e.natAbs:ℤ)=e := Int.natAbs_of_nonneg he.le
  have hdpos : 0<e.natAbs := Int.natAbs_pos.mpr (by omega)
  have hdiv := Int.natAbs_dvd_natAbs.mpr (apAt_dvd_sub hA hc hp)
  refine ⟨e.natAbs,hdpos,hdiv,?_⟩
  have hb := apAt_rebase hA hc
  obtain ⟨_he,lo,hi,hr⟩ := hb
  have hcB := (hr c).mp hc
  have hpB := (hr p).mp hp
  ext x
  constructor
  · rintro hx
    obtain ⟨hxA,hxI⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_filter.mpr ⟨hxI,by rw [hdcast]; exact apAt_dvd_sub hA hc hxA⟩
  · rintro hx
    obtain ⟨hxI,hdx⟩ := Finset.mem_filter.mp hx
    have hxB := Finset.mem_Icc.mp hxI
    rw [hdcast] at hdx
    exact Finset.mem_inter.mpr ⟨(hr x).mpr ⟨by omega,by omega,hdx⟩,hxI⟩

theorem actual_incompatible_trace_code {S : Finset ℤ} {c p : ℤ}
    (hc : c∈S) (hcover : AllCovered S c p)
    (hbad : ¬IsAP (Trace S c p)) :
    ∃ d e:ℕ,0<d ∧ 0<e ∧ d∣Distance c p ∧ e∣Distance c p ∧ IncompatibleCode S c p d e := by
  have hcI : c∈Finset.Icc (min c p) (max c p) := Finset.mem_Icc.mpr ⟨min_le_left _ _,le_max_left _ _⟩
  obtain ⟨Q,hQ⟩ := actual_intrinsic_pair_exists (Finset.mem_inter.mpr ⟨hc,hcI⟩) hbad
  obtain ⟨x,y,_hxy,rfl⟩ := Finset.card_eq_two.mp hQ.1
  have hxT := hQ.2.2.1 (by simp : x∈({x,y}:Finset ℤ))
  have hyT := hQ.2.2.1 (by simp : y∈({x,y}:Finset ℤ))
  obtain ⟨A,hAP,hAx,hAS⟩ := hcover x (Finset.mem_inter.mp hxT).1
  obtain ⟨B,hBP,hBy,hBS⟩ := hcover y (Finset.mem_inter.mp hyT).1
  obtain ⟨d,hd,hdd,hAd⟩ := actual_AP_trace_segment (c:=c) (p:=p) hAP (hAx (by simp)) (hAx (by simp))
  obtain ⟨e,he,hed,hBe⟩ := actual_AP_trace_segment (c:=c) (p:=p) hBP (hBy (by simp)) (hBy (by simp))
  have hdc : c∈Segment c p d := hAd ▸ Finset.mem_inter.mpr ⟨hAx (by simp),hcI⟩
  have hdx : x∈Segment c p d := hAd ▸ Finset.mem_inter.mpr ⟨hAx (by simp),(Finset.mem_inter.mp hxT).2⟩
  have hey : y∈Segment c p e := hBe ▸ Finset.mem_inter.mpr ⟨hBy (by simp),(Finset.mem_inter.mp hyT).2⟩
  refine ⟨d,e,hd,he,hdd,hed,?_,?_,?_⟩
  · rw [←hAd]; exact Finset.inter_subset_left.trans hAS
  · rw [←hBe]; exact Finset.inter_subset_left.trans hBS
  · rintro ⟨U,hUP,hCU,hUS⟩
    apply (intrinsic_trace_lift hQ).2.2.2
    refine ⟨U,hUP,?_,hUS⟩
    exact Finset.insert_subset_iff.mpr ⟨hCU (Finset.mem_union_left _ hdc),
      Finset.insert_subset_iff.mpr ⟨hCU (Finset.mem_union_left _ hdx),
        Finset.singleton_subset_iff.mpr (hCU (Finset.mem_union_right _ hey))⟩⟩

theorem actual_trace_code_private {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {S T : Finset ℤ} {c p : ℤ} {d e : ℕ} (hF : Legal Ω F) (hS : S∈F) (hT : T∈F)
    (hcode : IncompatibleCode S c p d e) (hdT : Segment c p d⊆T) (heT : Segment c p e⊆T) : S=T := by
  by_contra hne
  apply hcode.2.2
  refine ⟨S∩T,hF.2 S hS T hT hne,?_,Finset.inter_subset_left⟩
  exact Finset.subset_inter (Finset.union_subset hcode.1 hcode.2.1) (Finset.union_subset hdT heT)

theorem actual_crooked_trace_family_bound {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {c : ℤ} (hF : Legal Ω F) (hc : ∀ S∈F,c∈S)
    (p : {S // S∈F}→ℤ) (hp : ∀ S,p S∈S.val ∧ p S≠c)
    (hcover : ∀ S,AllCovered S.val c (p S)) (hbad : ∀ S,¬IsAP (Trace S.val c (p S))) :
    F.card≤∑ q∈Ω,((Distance c q).divisors.card)^2 := by
  let X := {S // S∈F}
  have hex : ∀ S:X,∃ d e:ℕ,0<d ∧ 0<e ∧ d∣Distance c (p S) ∧
      e∣Distance c (p S) ∧ IncompatibleCode S.val c (p S) d e :=
    fun S=>actual_incompatible_trace_code (hc S.val S.property) (hcover S) (hbad S)
  choose d e _hd _he hdd hed hcode using hex
  let U : Finset (Σ _ : ℤ,ℕ×ℕ) := Ω.sigma (fun q=>(Distance c q).divisors.product (Distance c q).divisors)
  let f : X→(Σ _ : ℤ,ℕ×ℕ) := fun S=>⟨p S,d S,e S⟩
  have hm : Set.MapsTo f (↑(Finset.univ:Finset X):Set X) U := by
    intro S _hS
    have hdist : Distance c (p S)≠0 := Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr (hp S).2)
    exact Finset.mem_sigma.mpr ⟨hF.1 S.val S.property (hp S).1,Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdd S,hdist⟩,Nat.mem_divisors.mpr ⟨hed S,hdist⟩⟩⟩
  have hi : Function.Injective f := by
    intro S T heq
    have hpST : p S=p T := congrArg Sigma.fst heq
    have hdST : d S=d T := congrArg (fun q:Σ _:ℤ,ℕ×ℕ=>q.2.1) heq
    have heST : e S=e T := congrArg (fun q:Σ _:ℤ,ℕ×ℕ=>q.2.2) heq
    apply Subtype.ext
    exact actual_trace_code_private hF S.property T.property (hcode S)
      (by simpa only [hpST,hdST] using (hcode T).1)
      (by simpa only [hpST,heST] using (hcode T).2.1)
  have hh := Finset.card_le_card_of_injOn f hm hi.injOn
  simpa [X,U,Finset.card_sigma,Finset.card_product,pow_two] using hh

theorem actual_bad_anchor_mem {F : Finset (Finset ℤ)} {S : Finset ℤ} {c : ℤ} {P : Finset ℤ}
    (hS : S∈BadMembers F c P) : Anchor S c P∈S.erase c∩P := by
  have hn := (Finset.mem_filter.mp hS).2.2.2.1
  simpa only [Anchor,dif_pos hn] using Finset.min'_mem (S.erase c∩P) hn

theorem actual_bad_anchor_covered {F : Finset (Finset ℤ)} {S : Finset ℤ} {c : ℤ} {P : Finset ℤ}
    (hS : S∈BadMembers F c P) : AllCovered S c (Anchor S c P) := by
  obtain ⟨_hSF,hc,_hbad,_hmet,hno⟩ := Finset.mem_filter.mp hS
  have ha := Finset.mem_inter.mp (actual_bad_anchor_mem hS)
  obtain ⟨hac,haS⟩ := Finset.mem_erase.mp ha.1
  apply all_covered_of_no_witness_at hc haS hac
  intro x hW
  exact Finset.disjoint_left.mp (hno _ hW) (by simp) ha.2

theorem actual_bad_trace_partition (F : Finset (Finset ℤ)) (c : ℤ) (P : Finset ℤ) :
    (CrookedTraceBad F c P).card+(APTraceBad F c P).card=(BadMembers F c P).card := by
  have hh := Finset.card_filter_add_card_filter_not (s:=BadMembers F c P)
    (fun S=>IsAP (Trace S c (Anchor S c P)))
  simpa only [CrookedTraceBad,APTraceBad,Nat.add_comm] using hh

theorem actual_restricted_bad_crooked_trace_bound {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hF : Legal Ω F) :
    (CrookedTraceBad F c P).card≤∑ q∈Ω,((Distance c q).divisors.card)^2 := by
  let C := CrookedTraceBad F c P
  have hCF : C⊆F := fun S hS=>(Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hlegal : Legal Ω C := ⟨fun S hS=>hF.1 S (hCF hS),
    fun S hS T hT he=>hF.2 S (hCF hS) T (hCF hT) he⟩
  apply actual_crooked_trace_family_bound hlegal
    (fun S hS=>(Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1)
    (fun S=>Anchor S.val c P)
  · intro S
    have ha := Finset.mem_inter.mp (actual_bad_anchor_mem (Finset.mem_filter.mp S.property).1)
    exact ⟨(Finset.mem_erase.mp ha.1).2,(Finset.mem_erase.mp ha.1).1⟩
  · intro S
    exact actual_bad_anchor_covered (Finset.mem_filter.mp S.property).1
  · intro S
    exact (Finset.mem_filter.mp S.property).2

theorem actual_restricted_bad_residual_bound {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hF : Legal Ω F) :
    (BadMembers F c P).card≤(∑ q∈Ω,((Distance c q).divisors.card)^2)+(APTraceBad F c P).card := by
  have hb := actual_restricted_bad_crooked_trace_bound c P hF
  have hp := actual_bad_trace_partition F c P
  omega

theorem distance_cast (c p : ℤ) : (Distance c p:ℤ)=max c p-min c p := by
  by_cases h : c≤p
  · simp only [Distance,Int.natAbs_of_nonneg (by omega : 0≤p-c),max_eq_right h,min_eq_left h]
  · have hp : p≤c := by omega
    dsimp only [Distance]
    rw [show p-c= -(c-p) by ring,Int.natAbs_neg,
      Int.natAbs_of_nonneg (by omega : 0≤c-p),max_eq_left hp,min_eq_right hp]

theorem nat_divides_distance_iff (d : ℕ) (c p : ℤ) :
    d∣Distance c p ↔ (d:ℤ)∣p-c := by
  simpa only [Distance,Int.natAbs_natCast] using
    (show (d:ℤ).natAbs∣(p-c).natAbs ↔ (d:ℤ)∣p-c from Int.natAbs_dvd_natAbs)

theorem actual_AP_positive_step {A : Finset ℤ} {c : ℤ} (hAP : IsAP A) (hc : c∈A) :
    ∃ d:ℕ,0<d ∧ APAt (d:ℤ) c A := by
  obtain ⟨e,p,hA,_⟩ := (isAP_iff_exists_APAt A).mp hAP
  have he := hA.1
  refine ⟨e.natAbs,Int.natAbs_pos.mpr (by omega),?_⟩
  rw [Int.natAbs_of_nonneg he.le]
  exact apAt_rebase hA hc

theorem actual_segment_subset_AP {A : Finset ℤ} {c p : ℤ} {d : ℕ}
    (hA : APAt (d:ℤ) c A) (hc : c∈A) (hp : p∈A) : Segment c p d⊆A := by
  obtain ⟨_hd,lo,hi,hr⟩ := hA
  have hcB := (hr c).mp hc
  have hpB := (hr p).mp hp
  intro x hx
  obtain ⟨hxI,hdx⟩ := Finset.mem_filter.mp hx
  have hxB := Finset.mem_Icc.mp hxI
  exact (hr x).mpr ⟨by omega,by omega,hdx⟩

theorem segment_first_two {c p : ℤ} {d : ℕ} (hcp : p≠c) (hd : 0<d)
    (hdiv : d∣Distance c p) :
    min c p∈Segment c p d ∧ min c p+(d:ℤ)∈Segment c p d := by
  have hD : 0<Distance c p := Int.natAbs_pos.mpr (sub_ne_zero.mpr hcp)
  have hle : (d:ℤ)≤max c p-min c p := by
    rw [←distance_cast]
    exact_mod_cast Nat.le_of_dvd hD hdiv
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  have hdc := (nat_divides_distance_iff d c p).mp hdiv
  have hdmin : (d:ℤ)∣min c p-c := by
    rcases le_total c p with h|h
    · simp only [min_eq_left h,sub_self,dvd_zero]
    · simpa only [min_eq_right h] using hdc
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,min_le_max⟩,hdmin⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    convert Int.dvd_add hdmin (dvd_refl (d:ℤ)) using 1
    ring

theorem actual_AP_trace_forces_grid {S : Finset ℤ} {c p : ℤ}
    (hc : c∈S) (hp : p∈S) (hpc : p≠c) (hcover : AllCovered S c p)
    (hAP : IsAP (Trace S c p)) :
    ∃ d:ℕ,0<d ∧ d∣Distance c p ∧ APAt (d:ℤ) c (Trace S c p) ∧
      ∀ x∈S,d∣Distance c x := by
  have hcT : c∈Trace S c p := Finset.mem_inter.mpr ⟨hc,Finset.mem_Icc.mpr ⟨min_le_left _ _,le_max_left _ _⟩⟩
  have hpT : p∈Trace S c p := Finset.mem_inter.mpr ⟨hp,Finset.mem_Icc.mpr ⟨min_le_right _ _,le_max_right _ _⟩⟩
  obtain ⟨d,hd,hT⟩ := actual_AP_positive_step hAP hcT
  have hdd := (nat_divides_distance_iff d c p).mpr (apAt_dvd_sub hT hcT hpT)
  refine ⟨d,hd,hdd,hT,?_⟩
  intro x hx
  obtain ⟨A,hAP,hCA,hAS⟩ := hcover x hx
  obtain ⟨e,he,hA⟩ := actual_AP_positive_step hAP (hCA (by simp : c∈({c,p,x}:Finset ℤ)))
  have hcA := hCA (by simp : c∈({c,p,x}:Finset ℤ))
  have hpA := hCA (by simp : p∈({c,p,x}:Finset ℤ))
  have hxA := hCA (by simp : x∈({c,p,x}:Finset ℤ))
  have hed := (nat_divides_distance_iff e c p).mpr (apAt_dvd_sub hA hcA hpA)
  have hs : Segment c p e⊆Trace S c p := by
    intro y hy
    exact Finset.mem_inter.mpr ⟨hAS (actual_segment_subset_AP hA hcA hpA hy),(Finset.mem_filter.mp hy).1⟩
  obtain ⟨hu,hv⟩ := segment_first_two hpc he hed
  have hdeZ : (d:ℤ)∣(e:ℤ) := by
    convert apAt_dvd_sub hT (hs hu) (hs hv) using 1
    ring
  have hde : d∣e := by exact_mod_cast hdeZ
  exact hde.trans ((nat_divides_distance_iff e c x).mpr (apAt_dvd_sub hA hcA hxA))

theorem actual_right_neighbor_witness {S : Finset ℤ} {c a : ℤ}
    (hc : c∈S) (hbad : ¬IsAP S) (ha : a∈S) (hca : c<a)
    (hnear : ∀ y∈S,c<y → a≤y) : ∃ z,IntrinsicPair c S {a,z} := by
  by_contra hn
  have hcover := all_covered_of_no_witness_at hc ha (by omega : a≠c) (fun z h=>hn ⟨z,h⟩)
  apply hbad
  apply ExteriorWitness36.closed_at_right_neighbor_isAP hc ha hca hnear
  intro w hw x hx
  obtain ⟨A,hAP,hCA,hAS⟩ := hcover w hw
  exact hAS (PrivatePairExistence.completionAt_least hAP (hCA (by simp)) (hCA (by simp)) (hCA (by simp)) hx)

theorem actual_left_neighbor_witness {S : Finset ℤ} {c a : ℤ}
    (hc : c∈S) (hbad : ¬IsAP S) (ha : a∈S) (hac : a<c)
    (hnear : ∀ y∈S,y<c → y≤a) : ∃ z,IntrinsicPair c S {a,z} := by
  have hcR : -c∈Reflect37.Reflect S := (Reflect37.mem_reflect S (-c)).mpr (by simpa using hc)
  have haR : -a∈Reflect37.Reflect S := (Reflect37.mem_reflect S (-a)).mpr (by simpa using ha)
  have hbR : ¬IsAP (Reflect37.Reflect S) := fun h=>hbad ((Reflect37.reflect_isAP_iff S).mp h)
  have hnR : ∀ y∈Reflect37.Reflect S,-c<y → -a≤y := by
    intro y hy hcy
    have hh := hnear (-y) ((Reflect37.mem_reflect S y).mp hy) (by omega)
    omega
  obtain ⟨z,hz⟩ := actual_right_neighbor_witness hcR hbR haR (by omega : -c< -a) hnR
  refine ⟨-z,?_⟩
  have hh := Reflect37.reflect_intrinsic hz
  simp only [neg_neg,Reflect37.reflect_involutive] at hh
  simpa only [Reflect37.Reflect,Finset.image_insert,neg_neg,
    Finset.image_singleton] using hh

theorem actual_AP_trace_divisor_witness {S : Finset ℤ} {c p : ℤ}
    (hc : c∈S) (hp : p∈S) (hpc : p≠c) (hbad : ¬IsAP S)
    (hcover : AllCovered S c p) (hAP : IsAP (Trace S c p)) :
    ∃ a z:ℤ,IntrinsicPair c S {a,z} ∧ Distance c a∣Distance c z := by
  obtain ⟨d,hd,hdd,hT,hgrid⟩ := actual_AP_trace_forces_grid hc hp hpc hcover hAP
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  have hD : (d:ℤ)≤max c p-min c p := by
    rw [←distance_cast]
    exact_mod_cast Nat.le_of_dvd (Int.natAbs_pos.mpr (sub_ne_zero.mpr hpc)) hdd
  have hcT : c∈Trace S c p := Finset.mem_inter.mpr ⟨hc,Finset.mem_Icc.mpr ⟨min_le_left _ _,le_max_left _ _⟩⟩
  have hpT : p∈Trace S c p := Finset.mem_inter.mpr ⟨hp,Finset.mem_Icc.mpr ⟨min_le_right _ _,le_max_right _ _⟩⟩
  by_cases hcp : c<p
  · let a := c+(d:ℤ)
    have hseg : a∈Segment c p d := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by dsimp [a];omega,by dsimp [a];omega⟩,?_⟩
      dsimp [a]; simp
    have ha := (Finset.mem_inter.mp (actual_segment_subset_AP hT hcT hpT hseg)).1
    have hnear : ∀ y∈S,c<y → a≤y := by
      intro y hy hcy
      have hh := Int.le_of_dvd (by omega : 0<y-c) ((nat_divides_distance_iff d c y).mp (hgrid y hy))
      dsimp [a];omega
    obtain ⟨z,hz⟩ := actual_right_neighbor_witness hc hbad ha (by dsimp [a];omega) hnear
    refine ⟨a,z,hz,?_⟩
    have he : Distance c a=d := by simp [Distance,a]
    rw [he]
    exact hgrid z (hz.2.2.1 (by simp))
  · let a := c-(d:ℤ)
    have hseg : a∈Segment c p d := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by dsimp [a];omega,by dsimp [a];omega⟩,?_⟩
      dsimp [a]; simp
    have ha := (Finset.mem_inter.mp (actual_segment_subset_AP hT hcT hpT hseg)).1
    have hnear : ∀ y∈S,y<c → y≤a := by
      intro y hy hyc
      have hh := Int.le_of_dvd (by omega : 0<c-y)
        (by simpa only [neg_sub] using Int.dvd_neg.mpr ((nat_divides_distance_iff d c y).mp (hgrid y hy)))
      dsimp [a];omega
    obtain ⟨z,hz⟩ := actual_left_neighbor_witness hc hbad ha (by dsimp [a];omega) hnear
    refine ⟨a,z,hz,?_⟩
    have he : Distance c a=d := by simp [Distance,a]
    rw [he]
    exact hgrid z (hz.2.2.1 (by simp))

theorem distance_side_injective {c a b : ℤ} (hd : Distance c a=Distance c b)
    (hs : decide (c≤a)=decide (c≤b)) : a=b := by
  have haD := distance_cast c a
  have hbD := distance_cast c b
  have he : (Distance c a:ℤ)=(Distance c b:ℤ) := by exact_mod_cast hd
  by_cases ha : c≤a
  · have hb : c≤b := by by_contra hn; simp [ha,hn] at hs
    simp only [max_eq_right ha,min_eq_left ha] at haD
    simp only [max_eq_right hb,min_eq_left hb] at hbD
    omega
  · have hb : ¬c≤b := by intro h; simp [ha,h] at hs
    have hac : a≤c := by omega
    have hbc : b≤c := by omega
    simp only [max_eq_left hac,min_eq_right hac] at haD
    simp only [max_eq_left hbc,min_eq_right hbc] at hbD
    omega

theorem actual_AP_trace_family_bound {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {c : ℤ} (hF : Legal Ω F) (hc : ∀ S∈F,c∈S) (hbad : ∀ S∈F,¬IsAP S)
    (p : {S // S∈F}→ℤ) (hp : ∀ S,p S∈S.val ∧ p S≠c)
    (hcover : ∀ S,AllCovered S.val c (p S)) (hAP : ∀ S,IsAP (Trace S.val c (p S))) :
    F.card≤2*∑ q∈Ω,(Distance c q).divisors.card := by
  let X := {S // S∈F}
  have hex : ∀ S:X,∃ a z:ℤ,IntrinsicPair c S.val {a,z} ∧ Distance c a∣Distance c z :=
    fun S=>actual_AP_trace_divisor_witness (hc S.val S.property) (hp S).1 (hp S).2
      (hbad S.val S.property) (hcover S) (hAP S)
  choose a z hW hdiv using hex
  let U : Finset (Σ _ : ℤ,Bool×ℕ) := Ω.sigma (fun q=>
    (Finset.univ:Finset Bool).product (Distance c q).divisors)
  let f : X→(Σ _ : ℤ,Bool×ℕ) := fun S=>⟨z S,decide (c≤a S),Distance c (a S)⟩
  have hm : Set.MapsTo f (↑(Finset.univ:Finset X):Set X) U := by
    intro S _hS
    have hz : z S∈S.val := (hW S).2.2.1 (by simp)
    have hzc : z S≠c := by intro he;exact (hW S).2.1 (by simp [he])
    have hD : Distance c (z S)≠0 := Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr hzc)
    exact Finset.mem_sigma.mpr ⟨hF.1 S.val S.property hz,Finset.mem_product.mpr
      ⟨Finset.mem_univ _,Nat.mem_divisors.mpr ⟨hdiv S,hD⟩⟩⟩
  have hi : Function.Injective f := by
    intro S T he
    have hz : z S=z T := congrArg Sigma.fst he
    have hs : decide (c≤a S)=decide (c≤a T) := congrArg (fun q:Σ _:ℤ,Bool×ℕ=>q.2.1) he
    have hd : Distance c (a S)=Distance c (a T) := congrArg (fun q:Σ _:ℤ,Bool×ℕ=>q.2.2) he
    have ha := distance_side_injective hd hs
    apply Subtype.ext
    exact actual_intrinsic_member_eq hF S.property T.property (hc S.val S.property) (hc T.val T.property)
      (hW S) (by rw [ha,hz];exact (hW T).2.2.1)
  have hh := Finset.card_le_card_of_injOn f hm hi.injOn
  simpa [X,U,Finset.card_sigma,Finset.card_product,Finset.mul_sum] using hh

theorem actual_restricted_bad_AP_trace_bound {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hF : Legal Ω F) :
    (APTraceBad F c P).card≤2*∑ q∈Ω,(Distance c q).divisors.card := by
  let C := APTraceBad F c P
  have hCF : C⊆F := fun S hS=>(Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hlegal : Legal Ω C := ⟨fun S hS=>hF.1 S (hCF hS),
    fun S hS T hT he=>hF.2 S (hCF hS) T (hCF hT) he⟩
  apply actual_AP_trace_family_bound hlegal
    (fun S hS=>(Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1)
    (fun S hS=>(Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2.1)
    (fun S=>Anchor S.val c P)
  · intro S
    have ha := Finset.mem_inter.mp (actual_bad_anchor_mem (Finset.mem_filter.mp S.property).1)
    exact ⟨(Finset.mem_erase.mp ha.1).2,(Finset.mem_erase.mp ha.1).1⟩
  · intro S
    exact actual_bad_anchor_covered (Finset.mem_filter.mp S.property).1
  · intro S
    exact (Finset.mem_filter.mp S.property).2

def WitnessException (Ω : Finset ℤ) (c : ℤ) : ℕ :=
  (∑ q∈Ω,((Distance c q).divisors.card)^2)+2*∑ q∈Ω,(Distance c q).divisors.card

theorem actual_restricted_bad_family_bound {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hF : Legal Ω F) :
    (BadMembers F c P).card≤WitnessException Ω c := by
  have hC := actual_restricted_bad_crooked_trace_bound c P hF
  have hA := actual_restricted_bad_AP_trace_bound c P hF
  have hp := actual_bad_trace_partition F c P
  dsimp only [WitnessException]
  omega

theorem restricted_witness_bad_family_card_le {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {c : ℤ} {P : Finset ℤ} (hF : Legal Ω F) (hc : ∀ S∈F,c∈S)
    (hbad : ∀ S∈F,¬IsAP S) (hmet : ∀ S∈F,(S.erase c∩P).Nonempty)
    (hno : ∀ S∈F,∀ Q,IntrinsicPair c S Q → Disjoint Q P) : F.card≤WitnessException Ω c := by
  have he : BadMembers F c P=F := by
    apply Finset.filter_eq_self.mpr
    intro S hS
    exact ⟨hc S hS,hbad S hS,hmet S hS,hno S hS⟩
  simpa only [he] using actual_restricted_bad_family_bound c P hF

theorem actual_crooked_good_bad_partition (F : Finset (Finset ℤ)) (c : ℤ) (P : Finset ℤ)
    (hc : ∀ S∈F,¬IsAP S → c∈S)
    (hmet : ∀ S∈F,¬IsAP S → (S.erase c∩P).Nonempty) :
    (MeetingCrooked F c P).card+(BadMembers F c P).card=(PrivatePairExistence.CrookedMembers F).card := by
  have hd : Disjoint (MeetingCrooked F c P) (BadMembers F c P) := by
    apply Finset.disjoint_left.mpr
    intro S hg hb
    obtain ⟨_hSF,_hc,_hbad,Q,hQ,hQP⟩ := Finset.mem_filter.mp hg
    exact hQP ((Finset.mem_filter.mp hb).2.2.2.2 Q hQ)
  have he : MeetingCrooked F c P∪BadMembers F c P=PrivatePairExistence.CrookedMembers F := by
    ext S
    constructor
    · intro hS
      rcases Finset.mem_union.mp hS with hg|hb
      · obtain ⟨hSF,_hc,hbad,_hW⟩ := Finset.mem_filter.mp hg
        exact Finset.mem_filter.mpr ⟨hSF,hbad⟩
      · obtain ⟨hSF,_hc,hbad,_hmet,_hno⟩ := Finset.mem_filter.mp hb
        exact Finset.mem_filter.mpr ⟨hSF,hbad⟩
    · intro hS
      obtain ⟨hSF,hbad⟩ := Finset.mem_filter.mp hS
      by_cases hg : ∃ Q,IntrinsicPair c S Q ∧ ¬Disjoint Q P
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hSF,hc S hSF hbad,hbad,hg⟩)
      · apply Finset.mem_union_right
        refine Finset.mem_filter.mpr ⟨hSF,hc S hSF hbad,hbad,hmet S hSF hbad,?_⟩
        intro Q hQ
        by_contra hQP
        exact hg ⟨Q,hQ,hQP⟩
  rw [←he,Finset.card_union_of_disjoint hd]

theorem actual_restricted_crooked_interval_budget {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hF : Legal Ω F)
    (hc : ∀ S∈F,¬IsAP S → c∈S)
    (hmet : ∀ S∈F,¬IsAP S → (S.erase c∩P).Nonempty) :
    ∃ u v:ℤ,SupportedEnvelope F c u v ∧
      (PrivatePairExistence.CrookedMembers F).card+(StraddledIntervals F c).card≤
        (IntervalPool Ω c u v P).card+WitnessException Ω c := by
  obtain ⟨u,v,hE,hcount⟩ := actual_meeting_crooked_interval_budget c P hF
  have hb := actual_restricted_bad_family_bound c P hF
  have hp := actual_crooked_good_bad_partition F c P hc hmet
  exact ⟨u,v,hE,by omega⟩

theorem actual_avoider_meets_erase {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {S P : Finset ℤ} {c : ℤ} (hF : Legal Ω F) (hS : S∈F) (hP : P∈F)
    (hcS : c∈S) (hcP : c∉P) : (S.erase c∩P).Nonempty := by
  have hne : S≠P := by intro he;exact hcP (he ▸ hcS)
  obtain ⟨x,hx⟩ := isAP_nonempty (hF.2 S hS P hP hne)
  obtain ⟨hxS,hxP⟩ := Finset.mem_inter.mp hx
  exact ⟨x,Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨by intro he;exact hcP (he ▸ hxP),hxS⟩,hxP⟩⟩

theorem actual_avoider_crooked_interval_budget {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hF : Legal Ω F) (hP : P∈F) (hcP : c∉P)
    (hc : ∀ S∈F,¬IsAP S → c∈S) :
    ∃ u v:ℤ,SupportedEnvelope F c u v ∧
      (PrivatePairExistence.CrookedMembers F).card+(StraddledIntervals F c).card≤
        (IntervalPool Ω c u v P).card+WitnessException Ω c := by
  exact actual_restricted_crooked_interval_budget c P hF hc
    (fun S hS hbad=>actual_avoider_meets_erase hF hS hP (hc S hS hbad) hcP)

#print axioms all_covered_of_no_witness_at
#print axioms intrinsic_trace_lift
#print axioms actual_AP_trace_segment
#print axioms actual_incompatible_trace_code
#print axioms actual_trace_code_private
#print axioms actual_crooked_trace_family_bound
#print axioms actual_bad_anchor_mem
#print axioms actual_bad_anchor_covered
#print axioms actual_bad_trace_partition
#print axioms actual_restricted_bad_crooked_trace_bound
#print axioms actual_restricted_bad_residual_bound
#print axioms distance_cast
#print axioms nat_divides_distance_iff
#print axioms actual_AP_positive_step
#print axioms actual_segment_subset_AP
#print axioms segment_first_two
#print axioms actual_AP_trace_forces_grid
#print axioms actual_right_neighbor_witness
#print axioms actual_left_neighbor_witness
#print axioms actual_AP_trace_divisor_witness
#print axioms distance_side_injective
#print axioms actual_AP_trace_family_bound
#print axioms actual_restricted_bad_AP_trace_bound
#print axioms actual_restricted_bad_family_bound
#print axioms restricted_witness_bad_family_card_le
#print axioms actual_crooked_good_bad_partition
#print axioms actual_restricted_crooked_interval_budget
#print axioms actual_avoider_meets_erase
#print axioms actual_avoider_crooked_interval_budget
end
end JSP233.RestrictedWitness44
