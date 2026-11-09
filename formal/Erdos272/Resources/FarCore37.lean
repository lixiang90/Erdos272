module

public import Erdos272.Resources.TraceWitnessCodes36
public import Erdos272.Traces.DyadicTraceSupply36
public import Erdos272.Core.NearAP36
public import Erdos272.Counting.SharpInterval36
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Actual fixed-step maximal cores of finite integer sets, divisor-minimal
traces, and their structural witness geometry.  No witness count or witness
predicate is an input to the geometric theorems. -/
namespace JSP233.FarCore37
open StarCompletion APGeometry LongTerminal35 TraceWitnessCodes36
open DyadicTraceSupply36 NearAP36
open scoped Classical BigOperators
noncomputable section

def Segment (c p : ℤ) (d : ℕ) : Finset ℤ :=
  (Finset.Icc c p).filter (fun x => (d:ℤ)∣x-c)

theorem mem_segment (c p x : ℤ) (d : ℕ) :
    x∈Segment c p d ↔ c≤x ∧ x≤p ∧ (d:ℤ)∣x-c := by
  simp only [Segment,Finset.mem_filter,Finset.mem_Icc,and_assoc]

theorem prefix_APAt (c : ℤ) (d k : ℕ) (hd : 0<d) :
    APAt (d:ℤ) c (Prefix c d k) := by
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  refine ⟨hdZ,c,c+(k:ℤ)*(d:ℤ),?_⟩
  intro x
  constructor
  · rintro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hi' : i≤k := by have := Finset.mem_range.mp hi; omega
    refine ⟨?_,?_,?_⟩
    · have hh : (0:ℤ)≤(i:ℤ)*(d:ℤ) := by positivity
      omega
    · have hiZ : (i:ℤ)≤(k:ℤ) := by exact_mod_cast hi'
      nlinarith
    · exact ⟨i,by ring⟩
  · rintro ⟨hcx,hxk,q,hq⟩
    have hq0 : 0≤q := by nlinarith
    have hqk : q≤(k:ℤ) := by nlinarith
    apply Finset.mem_image.mpr
    refine ⟨q.toNat,Finset.mem_range.mpr (by omega),?_⟩
    rw [Int.toNat_of_nonneg hq0]
    nlinarith

theorem prefix_zero_mem (c : ℤ) (d k : ℕ) : c∈Prefix c d k := by
  exact Finset.mem_image.mpr ⟨0,Finset.mem_range.mpr (by omega),by simp⟩

theorem prefix_one_mem (c : ℤ) (d k : ℕ) (hk : 1≤k) : c+(d:ℤ)∈Prefix c d k := by
  exact Finset.mem_image.mpr ⟨1,Finset.mem_range.mpr (by omega),by simp⟩

theorem segment_APAt (c p : ℤ) (d : ℕ) (hd : 0<d) :
    APAt (d:ℤ) c (Segment c p d) := by
  exact ⟨by exact_mod_cast hd,c,p,fun x=>mem_segment c p x d⟩

theorem segment_mono_step {c p : ℤ} {d e : ℕ} (hed : e∣d) :
    Segment c p d⊆Segment c p e := by
  intro x hx
  obtain ⟨hcx,hxp,hdx⟩ := (mem_segment _ _ _ _).mp hx
  exact (mem_segment _ _ _ _).mpr ⟨hcx,hxp,(by exact_mod_cast hed : (e:ℤ)∣d).trans hdx⟩

theorem fixed_step_maximal_core {S V : Finset ℤ} {c : ℤ} {d : ℕ}
    (hVS : V⊆S) (hV : APAt (d:ℤ) c V) (hcV : c∈V) :
    ∃ U : Finset ℤ, V⊆U ∧ U⊆S ∧ APAt (d:ℤ) c U ∧ c∈U ∧
      ∀ A⊆S, APAt (d:ℤ) c A → c∈A → A⊆U := by
  let C := S.powerset.filter (fun U : Finset ℤ => V⊆U ∧ APAt (d:ℤ) c U)
  have hVC : V∈C := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hVS,Finset.Subset.refl _,hV⟩
  obtain ⟨U,hUC,hmax⟩ := Finset.exists_max_image C Finset.card ⟨V,hVC⟩
  obtain ⟨hUS,hVU,hU⟩ := Finset.mem_filter.mp hUC
  have hUS' := Finset.mem_powerset.mp hUS
  have hcU := hVU hcV
  refine ⟨U,hVU,hUS',hU,hcU,?_⟩
  intro A hAS hA hcA
  have hu : APAt (d:ℤ) c (U∪A) := by
    simpa only [APAt,Finset.mem_union] using
      PrivateUnion.union_APAt (d:ℤ) c (fun x=>x∈U) (fun x=>x∈A) hU hA hcU hcA
  have hUA : U∪A∈C := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.union_subset hUS' hAS),
      hVU.trans Finset.subset_union_left,hu⟩
  have he := Finset.eq_of_subset_of_card_le Finset.subset_union_left (hmax _ hUA)
  exact he ▸ Finset.subset_union_right

theorem cover_step_dvd_of_coprime {A : Finset ℤ} {c z : ℤ} {d i : ℕ}
    (hAP : IsAP A) (hcA : c∈A) (hyA : c+(i:ℤ)*(d:ℤ)∈A) (hzA : z∈A)
    (hcop : Nat.Coprime i (z-c).natAbs) :
    ∃ e : ℕ, 0<e ∧ e∣d ∧ APAt (e:ℤ) c A := by
  obtain ⟨e,p,hA,_⟩ := (isAP_iff_exists_APAt _).mp hAP
  have he0 := hA.1
  have heabs : (e.natAbs:ℤ)=e := Int.natAbs_of_nonneg (by omega)
  have hy : e∣(i:ℤ)*(d:ℤ) := by
    convert apAt_dvd_sub hA hcA hyA using 1
    ring
  have hz : e∣z-c := apAt_dvd_sub hA hcA hzA
  have hyN : e.natAbs∣i*d := by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hy
  have hzN : e.natAbs∣(z-c).natAbs := Int.natAbs_dvd_natAbs.mpr hz
  have hecop : Nat.Coprime e.natAbs i := (hcop.of_dvd_right hzN).symm
  refine ⟨e.natAbs,Int.natAbs_pos.mpr (by omega),hecop.dvd_of_dvd_mul_left hyN,?_⟩
  rw [heabs]
  exact apAt_rebase hA hcA

theorem actual_minimal_trace_witness_core {S : Finset ℤ} {c p : ℤ} {d : ℕ}
    (hcp : c<p) (hd : 0<d)
    (htrace : Segment c p d⊆S)
    (hmin : ∀ e : ℕ, 0<e → e∣d → Segment c p e⊆S → d≤e) :
    ∃ U : Finset ℤ, U⊆S ∧ APAt (d:ℤ) c U ∧ Segment c p d⊆U ∧
      ∀ z ∈ S, p ≤ z → z ∉ U → ∀ i : ℕ, 0 < i → (c+(i:ℤ)*(d:ℤ)) ∈ U →
        Nat.Coprime i (z-c).natAbs → IntrinsicPair c S {c+(i:ℤ)*(d:ℤ),z} := by
  have hcT : c∈Segment c p d := (mem_segment _ _ _ _).mpr ⟨le_rfl,hcp.le,by simp⟩
  obtain ⟨U,hTU,hUS,hU,hcU,hmax⟩ := fixed_step_maximal_core htrace (segment_APAt c p d hd) hcT
  refine ⟨U,hUS,hU,hTU,?_⟩
  intro z hz hpz hzU i hi hyU hcop
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  have hiZ : (0:ℤ) < i := by exact_mod_cast hi
  have hcy : c<c+(i:ℤ)*(d:ℤ) := by nlinarith
  have hyz : c+(i:ℤ)*(d:ℤ)≠z := fun he=>hzU (he ▸ hyU)
  refine ⟨by simp [hyz],?_,?_,?_⟩
  · simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  · simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro (hUS hyU) hz
  · rintro ⟨A,hAP,hCA,hAS⟩
    have hcA : c∈A := hCA (by simp)
    have hyA : c+(i:ℤ)*(d:ℤ)∈A := hCA (by simp)
    have hzA : z∈A := hCA (by simp)
    obtain ⟨e,he,hed,hA⟩ := cover_step_dvd_of_coprime hAP hcA hyA hzA hcop
    have hTeA : Segment c p e⊆A := by
      intro x hx
      obtain ⟨hcx,hxp,hex⟩ := (mem_segment _ _ _ _).mp hx
      exact apAt_fill hA hcA hzA hcx (hxp.trans hpz) hex
    have hde := hmin e he hed (hTeA.trans hAS)
    have heq : e=d := Nat.le_antisymm (Nat.le_of_dvd hd hed) hde
    rw [heq] at hA
    exact hzU (hmax A hAS hA hcA hzA)

theorem actual_right_prefix {U : Finset ℤ} {c : ℤ} {d : ℕ}
    (hd : 0<d) (hU : APAt (d:ℤ) c U) (hc : c∈U) (hv : c+(d:ℤ)∈U) :
    ∃ k : ℕ, 1≤k ∧ U.filter (fun x=>c≤x)=Prefix c d k := by
  have hne : U.Nonempty := ⟨c,hc⟩
  let v := U.max' hne
  have hvU : v∈U := Finset.max'_mem U hne
  have hcv : c+(d:ℤ)≤v := Finset.le_max' U (c+(d:ℤ)) hv
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  obtain ⟨q,hq⟩ := apAt_dvd_sub hU hc hvU
  have hq1 : 1≤q := by nlinarith
  have hq0 : 0≤q := by omega
  have hqNat : (q.toNat:ℤ)=q := Int.toNat_of_nonneg hq0
  refine ⟨q.toNat,by omega,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hxU,hcx⟩ := Finset.mem_filter.mp hx
    have hxv : x≤v := Finset.le_max' U x hxU
    obtain ⟨i,hi⟩ := apAt_dvd_sub hU hc hxU
    have hi0 : 0 ≤ i := by nlinarith
    have hiq : i≤q := by nlinarith
    apply Finset.mem_image.mpr
    refine ⟨i.toNat,Finset.mem_range.mpr (by omega),?_⟩
    rw [Int.toNat_of_nonneg hi0]
    nlinarith
  · intro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hiq : i≤q.toNat := by have := Finset.mem_range.mp hi; omega
    have hiqZ : (i:ℤ)≤q := by
      have hh : (i:ℤ)≤(q.toNat:ℤ) := by exact_mod_cast hiq
      simpa only [hqNat] using hh
    have hci : c≤c+(i:ℤ)*(d:ℤ) := by
      have hh : (0:ℤ)≤(i:ℤ)*(d:ℤ) := by positivity
      omega
    apply Finset.mem_filter.mpr
    refine ⟨apAt_fill hU hc hvU hci (by nlinarith) ?_,hci⟩
    exact ⟨i,by ring⟩

def TraceSteps (S : Finset ℤ) (c p : ℤ) : Finset ℕ :=
  (p-c).natAbs.divisors.filter (fun d=>Segment c p d⊆S)

def MinimalTraceSteps (S : Finset ℤ) (c p : ℤ) : Finset ℕ :=
  (TraceSteps S c p).filter (fun d=>∀ e : ℕ, 0<e → e∣d → Segment c p e⊆S → d≤e)

theorem minimal_trace_step_data {S : Finset ℤ} {c p : ℤ} {d : ℕ}
    (hd : d∈MinimalTraceSteps S c p) :
    0<d ∧ d∣(p-c).natAbs ∧ Segment c p d⊆S ∧
      ∀ e : ℕ, 0<e → e∣d → Segment c p e⊆S → d≤e := by
  obtain ⟨hT,hmin⟩ := Finset.mem_filter.mp hd
  obtain ⟨hdiv,hS⟩ := Finset.mem_filter.mp hT
  exact ⟨Nat.pos_of_mem_divisors hdiv,(Nat.mem_divisors.mp hdiv).1,hS,hmin⟩

theorem exists_divisor_minimal_trace {S : Finset ℤ} {c p : ℤ} {d : ℕ}
    (hd : 0<d) (htrace : Segment c p d⊆S) :
    ∃ e : ℕ, 0<e ∧ e∣d ∧ Segment c p e⊆S ∧
      ∀ f : ℕ, 0<f → f∣e → Segment c p f⊆S → e≤f := by
  let D := d.divisors.filter (fun e=>Segment c p e⊆S)
  have hdD : d∈D := Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨dvd_refl _,by omega⟩,htrace⟩
  have hD : D.Nonempty := ⟨d,hdD⟩
  let e := D.min' hD
  obtain ⟨hed,heS⟩ := Finset.mem_filter.mp (Finset.min'_mem D hD)
  refine ⟨e,Nat.pos_of_mem_divisors hed,(Nat.mem_divisors.mp hed).1,heS,?_⟩
  intro f hf hfe hfS
  apply Finset.min'_le D f
  exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
    ⟨hfe.trans (Nat.mem_divisors.mp hed).1,by omega⟩,hfS⟩

theorem actual_minimal_trace_prefix_family {S : Finset ℤ} {c p : ℤ} (hcp : c<p) :
    ∃ k : ℕ→ℕ, ∀ d∈MinimalTraceSteps S c p,
      1≤k d ∧ Prefix c d (k d)⊆S ∧ Segment c p d⊆Prefix c d (k d) ∧
      ∀ z ∈ S, p≤z → z∉Prefix c d (k d) → ∀ i : ℕ, 0 < i → i≤k d →
        Nat.Coprime i (z-c).natAbs → IntrinsicPair c S {c+(i:ℤ)*(d:ℤ),z} := by
  have hex : ∀ d : ℕ, ∃ k : ℕ, d∈MinimalTraceSteps S c p →
      1≤k ∧ Prefix c d k⊆S ∧ Segment c p d⊆Prefix c d k ∧
      ∀ z ∈ S, p≤z → z∉Prefix c d k → ∀ i : ℕ, 0 < i → i≤k →
        Nat.Coprime i (z-c).natAbs → IntrinsicPair c S {c+(i:ℤ)*(d:ℤ),z} := by
    intro d
    by_cases hdm : d∈MinimalTraceSteps S c p
    · obtain ⟨hd,hdiv,htrace,hmin⟩ := minimal_trace_step_data hdm
      obtain ⟨U,hUS,hU,hTU,hW⟩ := actual_minimal_trace_witness_core hcp hd htrace hmin
      have hddiv : (d:ℤ)∣p-c := Int.natCast_dvd.mpr hdiv
      have hdZ : (0:ℤ)<d := by exact_mod_cast hd
      have hdle : (d:ℤ)≤p-c := Int.le_of_dvd (by omega) hddiv
      have hcT : c∈Segment c p d := (mem_segment _ _ _ _).mpr ⟨le_rfl,hcp.le,by simp⟩
      have hvT : c+(d:ℤ)∈Segment c p d :=
        (mem_segment _ _ _ _).mpr ⟨by omega,by omega,by simp⟩
      obtain ⟨k,hk,hprefix⟩ := actual_right_prefix hd hU (hTU hcT) (hTU hvT)
      refine ⟨k,fun _=>⟨hk,?_,?_,?_⟩⟩
      · rw [←hprefix]
        exact (Finset.filter_subset _ _).trans hUS
      · intro x hx
        rw [←hprefix]
        exact Finset.mem_filter.mpr ⟨hTU hx,((mem_segment _ _ _ _).mp hx).1⟩
      · intro z hz hpz hzP i hi hik hcop
        have hzU : z∉U := by
          intro hzU
          apply hzP
          rw [←hprefix]
          exact Finset.mem_filter.mpr ⟨hzU,by omega⟩
        apply hW z hz hpz hzU i hi _ hcop
        have hy : c+(i:ℤ)*(d:ℤ)∈Prefix c d k :=
          Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),rfl⟩
        rw [←hprefix] at hy
        exact (Finset.mem_filter.mp hy).1
    · exact ⟨0,fun hh=>False.elim (hdm hh)⟩
  choose k hk using hex
  exact ⟨k,hk⟩

theorem trace_union_subset_minimal (S : Finset ℤ) {c p : ℤ} (hcp : c<p) :
    (TraceSteps S c p).biUnion (Segment c p)⊆
      (MinimalTraceSteps S c p).biUnion (Segment c p) := by
  intro x hx
  obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨hdiv,htrace⟩ := Finset.mem_filter.mp hd
  obtain ⟨e,he,hed,heS,hmin⟩ := exists_divisor_minimal_trace
    (Nat.pos_of_mem_divisors hdiv) htrace
  have heM : e∈MinimalTraceSteps S c p := Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨hed.trans (Nat.mem_divisors.mp hdiv).1,by omega⟩,heS⟩,hmin⟩
  exact Finset.mem_biUnion.mpr ⟨e,heM,segment_mono_step hed hxd⟩

def WitnessNeighbors (S : Finset ℤ) (c p : ℤ) : Finset ℤ :=
  S.filter (fun x=>IntrinsicPair c S {p,x})

theorem actual_trace_cover {S : Finset ℤ} {c p : ℤ}
    (hcp : c<p) (hc : c∈S) (hp : p∈S) :
    S∩Finset.Icc c p⊆(MinimalTraceSteps S c p).biUnion (Segment c p) ∪
      WitnessNeighbors S c p := by
  intro x hx
  obtain ⟨hxS,hxI⟩ := Finset.mem_inter.mp hx
  obtain ⟨hcx,hxp⟩ := Finset.mem_Icc.mp hxI
  by_cases hW : IntrinsicPair c S {p,x}
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxS,hW⟩)
  have hcover : ∃ A : Finset ℤ, IsAP A ∧ insert c {p,x}⊆A ∧ A⊆S := by
    by_cases hxc : x=c
    · subst x
      refine ⟨{c,p},pair_isAP c p,?_,?_⟩
      · simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_insert,
          Finset.mem_singleton]
        tauto
      · simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
        exact ⟨hc,hp⟩
    by_cases hxp' : x=p
    · subst x
      refine ⟨{c,p},pair_isAP c p,?_,?_⟩
      · simp
      · simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
        exact ⟨hc,hp⟩
    by_contra hn
    apply hW
    refine ⟨by simp [Ne.symm hxp'],?_,?_,hn⟩
    · simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
    · simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hp,hxS⟩
  obtain ⟨A,hAP,hCA,hAS⟩ := hcover
  have hcA := hCA (show c∈insert c {p,x} by simp)
  have hpA := hCA (show p∈insert c {p,x} by simp)
  have hxA := hCA (show x∈insert c {p,x} by simp)
  obtain ⟨e,a,hA,_⟩ := (isAP_iff_exists_APAt _).mp hAP
  have he : 0<e := hA.1
  have heabs : (e.natAbs:ℤ)=e := Int.natAbs_of_nonneg (by omega)
  have hep := apAt_dvd_sub hA hcA hpA
  have hdiv : e.natAbs∣(p-c).natAbs := Int.natAbs_dvd_natAbs.mpr hep
  have hsegment : Segment c p e.natAbs⊆S := by
    intro y hy
    obtain ⟨hcy,hyp,hedy⟩ := (mem_segment _ _ _ _).mp hy
    rw [heabs] at hedy
    exact hAS (apAt_fill hA hcA hpA hcy hyp hedy)
  have heT : e.natAbs∈TraceSteps S c p := Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hdiv,by omega⟩,hsegment⟩
  apply Finset.mem_union_left
  apply trace_union_subset_minimal S hcp
  apply Finset.mem_biUnion.mpr
  refine ⟨e.natAbs,heT,(mem_segment _ _ _ _).mpr ⟨hcx,hxp,?_⟩⟩
  rw [heabs]
  exact apAt_dvd_sub hA hcA hxA

theorem actual_trace_card_cover {S : Finset ℤ} {c p : ℤ}
    (hcp : c<p) (hc : c∈S) (hp : p∈S) :
    (S∩Finset.Icc c p).card≤
      ((MinimalTraceSteps S c p).biUnion (Segment c p)).card+
        (WitnessNeighbors S c p).card :=
  (Finset.card_le_card (actual_trace_cover hcp hc hp)).trans (Finset.card_union_le _ _)

theorem actual_minimal_trace_codes {S Z : Finset ℤ} {c p : ℤ}
    (hcp : c<p) (I : Finset ℕ) (hI : I⊆MinimalTraceSteps S c p)
    (hZS : Z⊆S) (hpZ : ∀ z∈Z,p≤z) :
    ∃ k : ℕ→ℕ,
      (∀ d∈I, 1≤k d ∧ Prefix c d (k d)⊆S ∧ Segment c p d⊆Prefix c d (k d)) ∧
      (Disjoint Z (I.biUnion (fun d=>Prefix c d (k d))) →
        (∑ z∈Z,∑ d∈I,(PrimePrefix35.CoprimePrefix
          ((p-c).natAbs*(z-c).natAbs) (k d)).card)≤(StructuralPairs c S).card) := by
  obtain ⟨k,hk⟩ := actual_minimal_trace_prefix_family (S:=S) hcp
  refine ⟨k,fun d hd=>⟨(hk d (hI hd)).1,(hk d (hI hd)).2.1,
    (hk d (hI hd)).2.2.1⟩,?_⟩
  intro hdis
  apply actual_variable_anchor_codes I k (Int.natAbs_pos.mpr (by omega))
    (fun d hd=>(minimal_trace_step_data (hI hd)).2.1)
    (fun d hd i hi hik=>Finset.mem_biUnion.mpr
      ⟨d,hd,Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),rfl⟩⟩) hdis
  intro z hz d hd i hi hik hcop
  apply (hk d (hI hd)).2.2.2 z (hZS hz) (hpZ z hz) _ i hi hik hcop
  intro hzP
  exact Finset.disjoint_left.mp hdis hz (Finset.mem_biUnion.mpr ⟨d,hd,hzP⟩)

theorem proper_divisor_double {e d : ℕ} (hed : e∣d) (hlt : e<d) :
    2*e≤d := by
  obtain ⟨q,hq⟩ := hed
  have hq2 : 2≤q := by nlinarith
  nlinarith

theorem actual_minimal_long_prefix_core {S : Finset ℤ} {c : ℤ} {d K : ℕ}
    (hd : 0<d) (hprefix : Prefix c d K⊆S)
    (hmin : ∀ e : ℕ, 0<e → Prefix c e K⊆S → d≤e) :
    ∃ U : Finset ℤ, U⊆S ∧ APAt (d:ℤ) c U ∧ Prefix c d K⊆U ∧
      ∀ z ∈ S, z∉U → ∀ i : ℕ, 0 < i → i≤K → K≤2*i →
        Nat.Coprime i (z-c).natAbs → IntrinsicPair c S {c+(i:ℤ)*(d:ℤ),z} := by
  obtain ⟨U,hPU,hUS,hU,hcU,hmax⟩ :=
    fixed_step_maximal_core hprefix (prefix_APAt c d K hd) (prefix_zero_mem c d K)
  refine ⟨U,hUS,hU,hPU,?_⟩
  intro z hz hzU i hi hiK hKi hcop
  have hiP : c+(i:ℤ)*(d:ℤ)∈Prefix c d K :=
    Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),rfl⟩
  have hyU := hPU hiP
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  have hiZ : (0:ℤ) < i := by exact_mod_cast hi
  have hcy : c<c+(i:ℤ)*(d:ℤ) := by nlinarith
  have hzc : z≠c := fun he=>hzU (he.symm ▸ hcU)
  have hyz : c+(i:ℤ)*(d:ℤ)≠z := fun he=>hzU (he ▸ hyU)
  refine ⟨by simp [hyz],?_,?_,?_⟩
  · simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  · simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hUS hyU,hz⟩
  · rintro ⟨A,hAP,hCA,hAS⟩
    have hcA : c∈A := hCA (by simp)
    have hyA : c+(i:ℤ)*(d:ℤ)∈A := hCA (by simp)
    have hzA : z∈A := hCA (by simp)
    obtain ⟨e,he,hed,hA⟩ := cover_step_dvd_of_coprime hAP hcA hyA hzA hcop
    by_cases heq : e=d
    · rw [heq] at hA
      exact hzU (hmax A hAS hA hcA hzA)
    · have heD : e≤d := Nat.le_of_dvd hd hed
      have hdouble := proper_divisor_double hed (by omega)
      have hsmall : Prefix c e K⊆S := by
        intro x hx
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
        have hjK : j≤K := by have := Finset.mem_range.mp hj; omega
        have heZ : (0:ℤ)<e := by exact_mod_cast he
        have hcj : c≤c+(j:ℤ)*(e:ℤ) := by
          have hh : (0:ℤ)≤(j:ℤ)*(e:ℤ) := by positivity
          omega
        have hjKZ : (j:ℤ)≤K := by exact_mod_cast hjK
        have hdoubleZ : (2:ℤ)*e≤d := by exact_mod_cast hdouble
        have hKiZ : (K:ℤ)≤2*(i:ℤ) := by exact_mod_cast hKi
        apply hAS (apAt_fill hA hcA hyA hcj (by nlinarith) ?_)
        exact ⟨j,by ring⟩
      have hh := hmin e he hsmall
      omega

theorem actual_minimal_long_prefix_exists {S : Finset ℤ} {c : ℤ} {K : ℕ}
    (hex : ∃ d : ℕ, 0<d ∧ Prefix c d K⊆S) :
    ∃ d : ℕ, 0<d ∧ Prefix c d K⊆S ∧
      ∀ e : ℕ, 0<e → Prefix c e K⊆S → d≤e := by
  refine ⟨Nat.find hex,(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩
  intro e he hP
  exact Nat.find_min' hex ⟨he,hP⟩

theorem actual_long_prefix_codes {S : Finset ℤ} {c : ℤ} {d K : ℕ}
    (hd : 0<d) (hprefix : Prefix c d K⊆S)
    (hmin : ∀ e : ℕ, 0<e → Prefix c e K⊆S → d≤e) :
    ∃ U : Finset ℤ, U⊆S ∧ APAt (d:ℤ) c U ∧ Prefix c d K⊆U ∧
      (∑ z∈S\U,(SquarefreeSupply35.IntervalCoprime (z-c).natAbs (K/2) K).card)≤
        (StructuralPairs c S).card := by
  obtain ⟨U,hUS,hAt,hPU,hW⟩ := actual_minimal_long_prefix_core hd hprefix hmin
  refine ⟨U,hUS,hAt,hPU,?_⟩
  let V := (S\U).sigma (fun z=>SquarefreeSupply35.IntervalCoprime (z-c).natAbs (K/2) K)
  let f : (Σ _ : ℤ,ℕ)→Finset ℤ := fun q=>{c+(q.2:ℤ)*(d:ℤ),q.1}
  have hs : ∀ q∈V, q.1∈S ∧ q.1∉U ∧ c+(q.2:ℤ)*(d:ℤ)∈U ∧ IntrinsicPair c S (f q) := by
    intro q hq
    obtain ⟨hz,hi⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hzS,hzU⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hiI,hcop⟩ := Finset.mem_filter.mp hi
    obtain ⟨hhalf,hiK⟩ := Finset.mem_Ioc.mp hiI
    have hi0 : 0<q.2 := by omega
    have hKi : K≤2*q.2 := by omega
    have hy : c+(q.2:ℤ)*(d:ℤ)∈Prefix c d K :=
      Finset.mem_image.mpr ⟨q.2,Finset.mem_range.mpr (by omega),rfl⟩
    exact ⟨hzS,hzU,hPU hy,hW q.1 hzS hzU q.2 hi0 hiK hKi hcop⟩
  have hmaps : Set.MapsTo f (V:Set (Σ _ : ℤ,ℕ)) (StructuralPairs c S) :=
    fun q hq=>structural_pair_mem.mpr (hs q hq).2.2.2
  have hinj : Set.InjOn f (V:Set (Σ _ : ℤ,ℕ)) := by
    rintro ⟨z,i⟩ ha ⟨w,j⟩ hb heq
    have hza := hs ⟨z,i⟩ ha
    have hwb := hs ⟨w,j⟩ hb
    change ({c+(i:ℤ)*d,z}:Finset ℤ)={c+(j:ℤ)*d,w} at heq
    have hzm : z∈({c+(j:ℤ)*d,w}:Finset ℤ) := by rw [←heq]; simp
    have hzw : z=w := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hzm
      exact hzm.resolve_left (fun hh=>hza.2.1 (hh.symm ▸ hwb.2.2.1))
    have hym : c+(i:ℤ)*d∈({c+(j:ℤ)*d,w}:Finset ℤ) := by rw [←heq]; simp
    have hy : c+(i:ℤ)*d=c+(j:ℤ)*d := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hym
      exact hym.resolve_right (fun hh=>hwb.2.1 (hh ▸ hza.2.2.1))
    have hdZ : (0:ℤ)<d := by exact_mod_cast hd
    have hij : i=j := by
      have hh : (i:ℤ)=j := by nlinarith
      exact_mod_cast hh
    cases hzw
    cases hij
    rfl
  simpa only [V,Finset.card_sigma] using Finset.card_le_card_of_injOn f hmaps hinj

theorem actual_long_prefix_many_witnesses {S : Finset ℤ} {c : ℤ} {K w : ℕ}
    (hex : ∃ d : ℕ, 0<d ∧ Prefix c d K⊆S)
    (homega : ∀ z∈S, z≠c → (z-c).natAbs.primeFactors.card≤w)
    (hK : 4*(w+1)*2^w≤K) :
    ∃ U : Finset ℤ, U⊆S ∧ IsAP U ∧
      (S\U).card*K≤4*(w+1)*(StructuralPairs c S).card := by
  obtain ⟨d,hd,hprefix,hmin⟩ := actual_minimal_long_prefix_exists hex
  obtain ⟨U,hUS,hU,hPU,hcount⟩ := actual_long_prefix_codes hd hprefix hmin
  have hcU := hPU (prefix_zero_mem c d K)
  refine ⟨U,hUS,(isAP_iff_exists_APAt _).mpr ⟨d,c,hU,hcU⟩,?_⟩
  have hrow : ∀ z∈S\U,K≤4*(w+1)*
      (SquarefreeSupply35.IntervalCoprime (z-c).natAbs (K/2) K).card := by
    intro z hz
    obtain ⟨hzS,hzU⟩ := Finset.mem_sdiff.mp hz
    have hzc : z≠c := fun he=>hzU (he.symm ▸ hcU)
    have hm : 0<(z-c).natAbs := Int.natAbs_pos.mpr (by omega)
    exact SharpInterval36.actual_half_interval_supply_sharp (z-c).natAbs K w hm
      (homega z hzS hzc) hK
  have hs := Finset.sum_le_sum hrow
  have hm := Nat.mul_le_mul_left (4*(w+1)) hcount
  simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at hs
  exact hs.trans hm

theorem actual_far_long_prefix_witness_bound {S : Finset ℤ} {c : ℤ} {K w : ℕ}
    (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S)
    (hex : ∃ d : ℕ, 0<d ∧ Prefix c d K⊆S)
    (homega : ∀ z∈S, z≠c → (z-c).natAbs.primeFactors.card≤w)
    (hK : 4*(w+1)*2^w≤K) :
    K^2≤4*(w+1)*(StructuralPairs c S).card := by
  obtain ⟨U,hUS,hAP,hbound⟩ := actual_long_prefix_many_witnesses hex homega hK
  have hrem := non_near_actual_AP_remainder hlarge hfar U hUS hAP
  have hh := Nat.mul_le_mul_right K hrem
  nlinarith only [hh,hbound]

theorem actual_biUnion_subfamily_between {α β : Type*} [DecidableEq α] [DecidableEq β]
    (J : Finset α) (R : α→Finset β) {K : ℕ} (hK : 0<K)
    (hsmall : ∀ d∈J,(R d).card≤K) (hlarge : K≤(J.biUnion R).card) :
    ∃ I : Finset α, I⊆J ∧ K≤(I.biUnion R).card ∧ (I.biUnion R).card≤2*K := by
  revert hsmall hlarge
  induction J using Finset.induction_on with
  | empty =>
    intro _ hlarge
    simp only [Finset.biUnion_empty,Finset.card_empty] at hlarge
    omega
  | @insert a J ha ih =>
    intro hsmall hlarge
    by_cases hJ : K≤(J.biUnion R).card
    · obtain ⟨I,hIJ,hlo,hhi⟩ := ih (fun d hd=>hsmall d (Finset.mem_insert_of_mem hd)) hJ
      exact ⟨I,hIJ.trans (Finset.subset_insert _ _),hlo,hhi⟩
    · refine ⟨insert a J,Finset.Subset.refl _,hlarge,?_⟩
      rw [Finset.biUnion_insert]
      have hh := Finset.card_union_le (R a) (J.biUnion R)
      have haK := hsmall a (Finset.mem_insert_self _ _)
      omega

theorem actual_short_prefix_witness_bound {S : Finset ℤ} {c p : ℤ} {K ell w : ℕ}
    (hcp : c<p) (hc : c∈S) (hp : p∈S) (hK : 0<K)
    (hhead : 2*K≤(S∩Finset.Icc c p).card)
    (htail : 4*K≤(S.filter (fun z=>p≤z)).card)
    (hneighbors : (WitnessNeighbors S c p).card≤K)
    (hno : ∀ d : ℕ, 0<d → ¬Prefix c d K⊆S)
    (hell : 1≤ell) (hfinite : K≤2^ell)
    (homega : ∀ z∈S, p≤z →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤w)
    (hsize : (2*ell*(w+1))^2≤K) :
    K^2≤2*ell*(StructuralPairs c S).card := by
  obtain ⟨k,hk⟩ := actual_minimal_trace_prefix_family (S:=S) hcp
  let J := MinimalTraceSteps S c p
  let R : ℕ→Finset ℤ := fun d=>Prefix c d (k d)
  have hshort : ∀ d∈J,k d<K := by
    intro d hd
    by_contra hn
    apply hno d (minimal_trace_step_data hd).1
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    apply (hk d hd).2.1
    exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega),rfl⟩
  have hsmall : ∀ d∈J,(R d).card≤K := by
    intro d hd
    exact (prefix_card_le c d (k d)).trans (by have := hshort d hd; omega)
  have htraceSub : J.biUnion (Segment c p)⊆J.biUnion R := by
    intro x hx
    obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨d,hd,(hk d hd).2.2.1 hxd⟩
  have hlarge : K≤(J.biUnion R).card := by
    have hh := actual_trace_card_cover hcp hc hp
    have htr := Finset.card_le_card htraceSub
    change (J.biUnion (Segment c p)).card≤_ at htr
    change (S∩Finset.Icc c p).card≤(J.biUnion (Segment c p)).card+_ at hh
    omega
  obtain ⟨I,hIJ,hIlow,hIhigh⟩ := actual_biUnion_subfamily_between J R hK hsmall hlarge
  let H := I.biUnion R
  let Z := (S.filter (fun z=>p≤z))\H
  have hZ : 2*K≤Z.card := by
    have hh := Finset.card_le_card_sdiff_add_card (s:=S.filter (fun z=>p≤z)) (t:=H)
    change (S.filter (fun z=>p≤z)).card≤Z.card+H.card at hh
    change H.card≤2*K at hIhigh
    omega
  have hZne : Z.Nonempty := Finset.card_pos.mp (by omega)
  have hdiv : ∀ d∈I,d∣(p-c).natAbs := fun d hd=>(minimal_trace_step_data (hIJ hd)).2.1
  have htrace : ∀ d∈I,Segment c p d⊆S := fun d hd=>(minimal_trace_step_data (hIJ hd)).2.2.1
  have hmin : ∀ d∈I,∀ e : ℕ, 0<e → e∣d → Segment c p e⊆S → d≤e :=
    fun d hd=>(minimal_trace_step_data (hIJ hd)).2.2.2
  have hend : ∀ d∈I,c+((p-c).natAbs:ℤ)∈Prefix c d (k d) := by
    intro d hd
    have he : c+((p-c).natAbs:ℤ)=p := by rw [Int.natAbs_of_nonneg (by omega : 0≤p-c)]; ring
    rw [he]
    apply (hk d (hIJ hd)).2.2.1
    exact (mem_segment _ _ _ _).mpr ⟨hcp.le,le_rfl,Int.natCast_dvd.mpr (hdiv d hd)⟩
  have hrow : ∀ z∈Z,K≤2*(∑ d∈I,k d) ∧ (∑ d∈I,k d)≤
      2*ell*(∑ d∈I,(PrimePrefix35.CoprimePrefix
        ((p-c).natAbs*(z-c).natAbs) (k d)).card) := by
    intro z hz
    obtain ⟨hzT,_⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzS,hpz⟩ := Finset.mem_filter.mp hzT
    have hpabs : 0<(p-c).natAbs := Int.natAbs_pos.mpr (by omega)
    have hzabs : 0<(z-c).natAbs := Int.natAbs_pos.mpr (by omega)
    apply actual_minimal_trace_supply c (p-c).natAbs
      ((p-c).natAbs*(z-c).natAbs) K ell w I (fun d=>Segment c p d⊆S) k hpabs
      (Nat.mul_pos hpabs hzabs) hdiv htrace hmin hend
      (fun d hd=>(hshort d (hIJ hd)).trans_le hfinite) (homega z hzS hpz)
      hIlow hell hsize
  have hcode : (∑ z∈Z,∑ d∈I,(PrimePrefix35.CoprimePrefix
      ((p-c).natAbs*(z-c).natAbs) (k d)).card)≤(StructuralPairs c S).card := by
    apply actual_variable_anchor_codes I k (Int.natAbs_pos.mpr (by omega)) hdiv
      (fun d hd i hi hik=>Finset.mem_biUnion.mpr
        ⟨d,hd,Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),rfl⟩⟩)
      (Finset.disjoint_left.mpr (fun z hz hzH=>(Finset.mem_sdiff.mp hz).2 hzH))
    intro z hz d hd i hi hik hcop
    obtain ⟨hzT,hzH⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzS,hpz⟩ := Finset.mem_filter.mp hzT
    apply (hk d (hIJ hd)).2.2.2 z hzS hpz _ i hi hik hcop
    exact fun hzR=>hzH (Finset.mem_biUnion.mpr ⟨d,hd,hzR⟩)
  obtain ⟨z,hz⟩ := hZne
  have hsumK := (hrow z hz).1
  have hs := Finset.sum_le_sum (fun z hz=>(hrow z hz).2)
  simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at hs
  have hpay := Nat.mul_le_mul_left (2*ell) hcode
  have hp1 := Nat.mul_le_mul_right (∑ d∈I,k d) hZ
  have hp2 := Nat.mul_le_mul_left K hsumK
  nlinarith only [hs,hpay,hp1,hp2]

theorem actual_middle_block {T : Finset ℤ} {K : ℕ} (hcard : 8*K≤T.card) :
    ∃ M : Finset ℤ, M⊆T ∧ M.card=K ∧ ∀ p∈M,
      2*K≤(T.filter (fun x=>x≤p)).card ∧ 4*K≤(T.filter (fun x=>p≤x)).card := by
  let f := T.orderEmbOfFin rfl
  let mid : Fin K→ℤ := fun i=>f ⟨2*K+i.val,by omega⟩
  have hinj : Function.Injective mid := by
    intro i j hij
    have hh := f.injective hij
    have hv := congrArg Fin.val hh
    apply Fin.ext
    change 2*K+i.val=2*K+j.val at hv
    omega
  refine ⟨Finset.univ.image mid,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact T.orderEmbOfFin_mem rfl _
  · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    constructor
    · let lo : Fin (2*K)→ℤ := fun j=>f ⟨j.val,by omega⟩
      have hlo : Function.Injective lo := by
        intro a b hab
        have hh := congrArg Fin.val (f.injective hab)
        exact Fin.ext hh
      have hmaps : Set.MapsTo lo (↑(Finset.univ:Finset (Fin (2*K))):Set (Fin (2*K)))
          (T.filter (fun x=>x≤mid i):Set ℤ) := by
        intro j _
        refine Finset.mem_filter.mpr ⟨T.orderEmbOfFin_mem rfl _,?_⟩
        apply f.monotone
        change j.val≤2*K+i.val
        omega
      simpa only [Finset.card_univ,Fintype.card_fin] using
        Finset.card_le_card_of_injOn lo hmaps hlo.injOn
    · let hi : Fin (4*K)→ℤ := fun j=>f ⟨4*K+j.val,by omega⟩
      have hhi : Function.Injective hi := by
        intro a b hab
        have hh := congrArg Fin.val (f.injective hab)
        apply Fin.ext
        change 4*K+a.val=4*K+b.val at hh
        omega
      have hmaps : Set.MapsTo hi (↑(Finset.univ:Finset (Fin (4*K))):Set (Fin (4*K)))
          (T.filter (fun x=>mid i≤x):Set ℤ) := by
        intro j _
        refine Finset.mem_filter.mpr ⟨T.orderEmbOfFin_mem rfl _,?_⟩
        apply f.monotone
        change 2*K+i.val≤4*K+j.val
        omega
      simpa only [Finset.card_univ,Fintype.card_fin] using
        Finset.card_le_card_of_injOn hi hmaps hhi.injOn

theorem actual_neighbors_double_count (S M : Finset ℤ) (c : ℤ) :
    (∑ p∈M,(WitnessNeighbors S c p).card)≤2*(StructuralPairs c S).card := by
  let A := M.sigma (WitnessNeighbors S c)
  let B := (StructuralPairs c S).sigma (fun Q=>Q)
  let f : (Σ _ : ℤ,ℤ)→(Σ _ : Finset ℤ,ℤ) := fun q=>⟨{q.1,q.2},q.1⟩
  have hs : ∀ q∈A,IntrinsicPair c S {q.1,q.2} := by
    intro q hq
    exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hq).2).2
  have hmaps : Set.MapsTo f (A:Set (Σ _ : ℤ,ℤ)) (B:Set (Σ _ : Finset ℤ,ℤ)) := by
    intro q hq
    exact Finset.mem_sigma.mpr ⟨structural_pair_mem.mpr (hs q hq),by simp [f]⟩
  have hinj : Set.InjOn f (A:Set (Σ _ : ℤ,ℤ)) := by
    rintro ⟨p,x⟩ hx ⟨q,y⟩ hy heq
    have hpq : p=q := congrArg (fun z : (Σ _ : Finset ℤ,ℤ)=>z.2) heq
    subst q
    have hpairs : ({p,x}:Finset ℤ)={p,y} := congrArg Sigma.fst heq
    have hpx : p≠x := by
      intro hh
      have hc := (hs ⟨p,x⟩ hx).1
      simp [hh] at hc
    have hxmem : x∈({p,y}:Finset ℤ) := by rw [←hpairs]; simp
    have hxy : x=y := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hxmem
      exact hxmem.resolve_left hpx.symm
    subst y
    rfl
  have hB : B.card=2*(StructuralPairs c S).card := by
    rw [Finset.card_sigma]
    have hh : (∑ Q∈StructuralPairs c S,Q.card)=∑ _Q∈StructuralPairs c S,(2:ℕ) :=
      Finset.sum_congr rfl (fun Q hQ=>(structural_pair_mem.mp hQ).1)
    simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm] using hh
  simpa only [A,Finset.card_sigma] using (Finset.card_le_card_of_injOn f hmaps hinj).trans_eq hB

theorem actual_no_long_right_prefix_witness_bound {S : Finset ℤ} {c : ℤ} {K ell w : ℕ}
    (hc : c∈S) (hK : 0<K) (hright : 8*K≤(S.filter (fun x=>c<x)).card)
    (hno : ∀ d : ℕ, 0<d → ¬Prefix c d K⊆S)
    (hell : 1≤ell) (hfinite : K≤2^ell)
    (homega : ∀ p∈S, c<p → ∀ z∈S, p≤z →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤w)
    (hsize : (2*ell*(w+1))^2≤K) :
    K^2≤2*ell*(StructuralPairs c S).card := by
  let T := S.filter (fun x=>c<x)
  obtain ⟨M,hMT,hMcard,hmiddle⟩ := actual_middle_block hright
  by_cases hsome : ∃ p∈M,(WitnessNeighbors S c p).card≤K
  · obtain ⟨p,hpM,hneigh⟩ := hsome
    obtain ⟨hpS,hcp⟩ := Finset.mem_filter.mp (hMT hpM)
    have hhead : 2*K≤(S∩Finset.Icc c p).card :=
      (hmiddle p hpM).1.trans (Finset.card_le_card (by
        intro x hx
        obtain ⟨hxT,hxp⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxS,hcx⟩ := Finset.mem_filter.mp hxT
        exact Finset.mem_inter.mpr ⟨hxS,Finset.mem_Icc.mpr ⟨hcx.le,hxp⟩⟩))
    have htail : 4*K≤(S.filter (fun x=>p≤x)).card :=
      (hmiddle p hpM).2.trans (Finset.card_le_card (by
        intro x hx
        obtain ⟨hxT,hpx⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxT).1,hpx⟩))
    exact actual_short_prefix_witness_bound hcp hc hpS hK hhead htail hneigh hno
      hell hfinite (homega p hpS hcp) hsize
  · have hneigh : ∀ p∈M,K≤(WitnessNeighbors S c p).card := by
      intro p hp
      by_contra hn
      exact hsome ⟨p,hp,by omega⟩
    have hlo := Finset.sum_le_sum hneigh
    simp only [Finset.sum_const,nsmul_eq_mul,hMcard] at hlo
    have hhi := actual_neighbors_double_count S M c
    have hm := Nat.mul_le_mul_right (2*(StructuralPairs c S).card) hell
    nlinarith only [hlo,hhi,hm]

theorem actual_far_right_witness_bound {S : Finset ℤ} {c : ℤ} {K ell w₁ w₂ : ℕ}
    (hc : c∈S) (hK : 0<K) (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S)
    (hright : 8*K≤(S.filter (fun x=>c<x)).card)
    (hell : 1≤ell) (hfinite : K≤2^ell)
    (homega₁ : ∀ z∈S, z≠c → (z-c).natAbs.primeFactors.card≤w₁)
    (homega₂ : ∀ p∈S, c<p → ∀ z∈S, p≤z →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤w₂)
    (hlong : 4*(w₁+1)*2^w₁≤K) (hshort : (2*ell*(w₂+1))^2≤K) :
    K^2≤max (4*(w₁+1)) (2*ell)*(StructuralPairs c S).card := by
  by_cases hex : ∃ d : ℕ,0<d ∧ Prefix c d K⊆S
  · have hh := actual_far_long_prefix_witness_bound hlarge hfar hex homega₁ hlong
    exact hh.trans (Nat.mul_le_mul_right _ (le_max_left _ _))
  · have hh := actual_no_long_right_prefix_witness_bound hc hK hright
      (fun d hd hpre=>hex ⟨d,hd,hpre⟩) hell hfinite homega₂ hshort
    exact hh.trans (Nat.mul_le_mul_right _ (le_max_right _ _))

#print axioms mem_segment
#print axioms prefix_APAt
#print axioms prefix_zero_mem
#print axioms prefix_one_mem
#print axioms segment_APAt
#print axioms segment_mono_step
#print axioms fixed_step_maximal_core
#print axioms cover_step_dvd_of_coprime
#print axioms actual_minimal_trace_witness_core
#print axioms actual_right_prefix
#print axioms minimal_trace_step_data
#print axioms exists_divisor_minimal_trace
#print axioms actual_minimal_trace_prefix_family
#print axioms trace_union_subset_minimal
#print axioms actual_trace_cover
#print axioms actual_trace_card_cover
#print axioms actual_minimal_trace_codes
#print axioms proper_divisor_double
#print axioms actual_minimal_long_prefix_core
#print axioms actual_minimal_long_prefix_exists
#print axioms actual_long_prefix_codes
#print axioms actual_long_prefix_many_witnesses
#print axioms actual_far_long_prefix_witness_bound
#print axioms actual_biUnion_subfamily_between
#print axioms actual_short_prefix_witness_bound
#print axioms actual_middle_block
#print axioms actual_neighbors_double_count
#print axioms actual_no_long_right_prefix_witness_bound
#print axioms actual_far_right_witness_bound
end
end JSP233.FarCore37
