module

public import Erdos272.Resources.JointResources31
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Intrinsic missing-completion pairs inside the actual rooted private pool.
The geometric lemmas below derive closure from the actual singleton pool. -/
namespace JSP233.SinglePrivate32
open StarCompletion PrivatePairExistence JointResources31 AffineLine30
open scoped Classical
noncomputable section

def IntrinsicPairs (c : ℤ) (S : Finset ℤ) : Finset (Finset ℤ) :=
  S.powerset.filter (fun Q => Q.card=2 ∧ c∉Q ∧
    ∃ u∈Q, ∃ v∈Q, ∃ x, CompletionAt c u v x ∧ x∉S)

theorem mem_intrinsicPairs (c : ℤ) (S Q : Finset ℤ) :
    Q∈IntrinsicPairs c S ↔ Q⊆S ∧ Q.card=2 ∧ c∉Q ∧
      ∃ u∈Q, ∃ v∈Q, ∃ x, CompletionAt c u v x ∧ x∉S := by
  simp only [IntrinsicPairs, Finset.mem_filter, Finset.mem_powerset]

theorem missing_pair_properties {c u v : ℤ} {S : Finset ℤ}
    (hc : c∈S) (hu : u∈S) (hv : v∈S)
    (hmiss : ∃ x, CompletionAt c u v x ∧ x∉S) :
    u≠c ∧ v≠c ∧ u≠v ∧ ¬IsAP (insert c ({u,v} : Finset ℤ)) := by
  obtain ⟨x,hx,hxn⟩ := hmiss
  have hb : ¬IsAP (insert c ({u,v} : Finset ℤ)) := by
    intro ha
    have hm := completionAt_least ha (by simp) (by simp) (by simp) hx
    have hsub : insert c ({u,v} : Finset ℤ) ⊆ S := by
      intro y hy
      simp only [Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    exact hxn (hsub hm)
  refine ⟨?_,?_,?_,hb⟩
  · intro he; subst u
    exact hb (by simpa using pair_isAP c v)
  · intro he; subst v
    exact hb (by simpa [Finset.insert_comm,Finset.pair_comm] using pair_isAP c u)
  · intro he; subst v
    exact hb (by simpa using pair_isAP c u)

theorem pair_mem_intrinsicPairs {c u v : ℤ} {S : Finset ℤ}
    (hc : c∈S) (hu : u∈S) (hv : v∈S)
    (hmiss : ∃ x, CompletionAt c u v x ∧ x∉S) :
    ({u,v} : Finset ℤ)∈IntrinsicPairs c S := by
  obtain ⟨huc,hvc,huv,hbad⟩ := missing_pair_properties hc hu hv hmiss
  apply (mem_intrinsicPairs c S _).mpr
  refine ⟨?_,by simp [huv],by simp [Ne.symm huc,Ne.symm hvc],u,by simp,v,by simp,hmiss⟩
  exact Finset.insert_subset_iff.mpr ⟨hu,Finset.singleton_subset_iff.mpr hv⟩

theorem intrinsicPairs_nonempty {c : ℤ} {S : Finset ℤ}
    (hc : c∈S) (hbad : ¬IsAP S) : (IntrinsicPairs c S).Nonempty := by
  obtain ⟨u,hu,v,hv,huc,hvc,huv,hmiss,hbadpair⟩ :=
    missing_completion_at_root_exists hc hbad
  exact ⟨{u,v},pair_mem_intrinsicPairs hc hu hv hmiss⟩

theorem intrinsic_pair_not_isAP {c : ℤ} {S Q : Finset ℤ}
    (hc : c∈S) (hQ : Q∈IntrinsicPairs c S) : ¬IsAP (insert c Q) := by
  obtain ⟨hsub,hcard,hroot,u,hu,v,hv,x,hx,hxn⟩ := (mem_intrinsicPairs c S Q).mp hQ
  intro ha
  have hm := completionAt_least ha (by simp) (by simp [hu]) (by simp [hv]) hx
  exact hxn (Finset.insert_subset_iff.mpr ⟨hc,hsub⟩ hm)

theorem intrinsic_pair_private {c : ℤ} {Ω : Finset ℤ} {G : Finset (Finset ℤ)}
    (hlegal : Legal Ω G) (hroot : Rooted G c) {S Q : Finset ℤ}
    (hSG : S∈G) (hQ : Q∈IntrinsicPairs c S) :
    ∀ T∈G, T≠S → ¬Q⊆T := by
  obtain ⟨hsub,hcard,hnot,u,hu,v,hv,x,hx,hxn⟩ := (mem_intrinsicPairs c S Q).mp hQ
  intro T hTG hTS hQT
  have hI := hlegal.2 S hSG T hTG hTS.symm
  have hm := completionAt_least hI
    (Finset.mem_inter.mpr ⟨hroot S hSG,hroot T hTG⟩)
    (Finset.mem_inter.mpr ⟨hsub hu,hQT hu⟩)
    (Finset.mem_inter.mpr ⟨hsub hv,hQT hv⟩) hx
  exact hxn (Finset.mem_inter.mp hm).1

theorem intrinsicPairs_subset_privatePool {c : ℤ} {Ω : Finset ℤ}
    {G : Finset (Finset ℤ)} (hlegal : Legal Ω G) (hroot : Rooted G c)
    {S : Finset ℤ} (hSG : S∈G) : IntrinsicPairs c S⊆PrivatePool c Ω G S := by
  intro Q hQ
  obtain ⟨hsub,hcard,hnot,hmiss⟩ := (mem_intrinsicPairs c S Q).mp hQ
  have hp := intrinsic_pair_private hlegal hroot hSG hQ
  have hb := intrinsic_pair_not_isAP (hroot S hSG) hQ
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hsub.trans (hlegal.1 S hSG)),
    hcard,hnot,hb,?_⟩,hsub,hp⟩
  intro T hTG hAP
  by_cases he : T=S
  · subst T
    intro _
    obtain ⟨u,hu,v,hv,x,hx,hxn⟩ := hmiss
    exact hxn (completionAt_least hAP (hroot S hSG) (hsub hu) (hsub hv) hx)
  · exact hp T hTG he

theorem intrinsicPairs_card_one_of_privatePool {c : ℤ} {Ω : Finset ℤ}
    {G : Finset (Finset ℤ)} (hlegal : Legal Ω G) (hroot : Rooted G c)
    {S : Finset ℤ} (hSG : S∈G) (hbad : ¬IsAP S)
    (hsingle : (PrivatePool c Ω G S).card=1) : (IntrinsicPairs c S).card=1 := by
  have hp := Finset.card_pos.mpr (intrinsicPairs_nonempty (hroot S hSG) hbad)
  have hl := Finset.card_le_card (intrinsicPairs_subset_privatePool hlegal hroot hSG)
  omega

theorem singletonPrivateLarge_intrinsic_card_one {c : ℤ} {Ω : Finset ℤ}
    {G : Finset (Finset ℤ)} (hlegal : Legal Ω G) (hroot : Rooted G c)
    {S : Finset ℤ} (hS : S∈SingletonPrivateLarge c Ω G) :
    (IntrinsicPairs c S).card=1 := by
  obtain ⟨hlarge,hsingle⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSG,hbad,hcard⟩ := Finset.mem_filter.mp hlarge
  exact intrinsicPairs_card_one_of_privatePool hlegal hroot hSG hbad hsingle

theorem completion_full_away_pair {S Q : Finset ℤ} (hz : 0∈S)
    (hunique : IntrinsicPairs 0 S={Q}) {u v : ℤ} (hu : u∈S) (hv : v∈S)
    (hne : ({u,v} : Finset ℤ)≠Q) : ∀ x, Completion u v x → x∈S := by
  intro x hx
  by_contra hxn
  have hm := pair_mem_intrinsicPairs hz hu hv
    ⟨x,by simpa only [CompletionAt,sub_zero] using hx,hxn⟩
  rw [hunique] at hm
  exact hne (Finset.mem_singleton.mp hm)

theorem minimum_abs_le_gcd_of_full_pair {S : Finset ℤ} {s a b : ℤ}
    (hmin : ∀ y∈S, y≠0 → s.natAbs≤y.natAbs) (ha0 : a≠0)
    (hfull : ∀ x, Completion a b x → x∈S) : s.natAbs≤Int.gcd a b := by
  have hp : 0<Int.gcd a b := Int.gcd_pos_of_ne_zero_left b ha0
  have hl : Int.gcd a b≤a.natAbs := Int.gcd_le_natAbs_left b ha0
  by_cases ha : 0≤a
  · have habs : (a.natAbs : ℤ)=a := Int.natAbs_of_nonneg ha
    have hc : Completion a b (Int.gcd a b : ℤ) := ⟨by omega,by omega,dvd_refl _⟩
    simpa using hmin _ (hfull _ hc) (by omega)
  · have habs : (a.natAbs : ℤ)=-a := by
      simpa using Int.natAbs_of_nonneg (show 0≤-a by omega)
    have hc : Completion a b (-(Int.gcd a b : ℤ)) :=
      ⟨by omega,by omega,dvd_neg.mpr (dvd_refl _)⟩
    simpa using hmin _ (hfull _ hc) (by omega)

theorem minimum_abs_gcd_of_full_pair {S : Finset ℤ} {s w : ℤ}
    (hs0 : s≠0) (hmin : ∀ y∈S, y≠0 → s.natAbs≤y.natAbs)
    (hfull : ∀ x, Completion s w x → x∈S) : Int.gcd s w=s.natAbs := by
  exact Nat.le_antisymm (Int.gcd_le_natAbs_left w hs0)
    (minimum_abs_le_gcd_of_full_pair hmin hs0 hfull)

theorem minimum_spoke_closed_isAP {S : Finset ℤ} {s : ℤ}
    (hz : 0∈S) (_hs : s∈S) (hs0 : s≠0)
    (hmin : ∀ y∈S, y≠0 → s.natAbs≤y.natAbs)
    (hspoke : ∀ w∈S, ∀ x, Completion s w x → x∈S) : IsAP S := by
  have hne : S.Nonempty := ⟨0,hz⟩
  let lo := S.min' hne
  let hi := S.max' hne
  have hlo : lo∈S := Finset.min'_mem S hne
  have hhi : hi∈S := Finset.max'_mem S hne
  have hp : 0<(s.natAbs : ℤ) := by have hh := Int.natAbs_pos.mpr hs0; omega
  refine ⟨s.natAbs,0,hp,lo,hi,?_,hz⟩
  intro x
  constructor
  · intro hx
    refine ⟨Finset.min'_le S x hx,Finset.le_max' S x hx,?_⟩
    have hg := minimum_abs_gcd_of_full_pair hs0 hmin (hspoke x hx)
    simpa [hg] using Int.gcd_dvd_right s x
  · intro hx
    have hlo0 : lo≤0 := Finset.min'_le S 0 hz
    have hhi0 : 0≤hi := Finset.le_max' S 0 hz
    by_cases hx0 : 0≤x
    · apply hspoke hi hhi x
      exact ⟨by omega,by omega,by
        simpa [minimum_abs_gcd_of_full_pair hs0 hmin (hspoke hi hhi)] using hx.2.2⟩
    · apply hspoke lo hlo x
      exact ⟨by omega,by omega,by
        simpa [minimum_abs_gcd_of_full_pair hs0 hmin (hspoke lo hlo)] using hx.2.2⟩

theorem minimum_mem_unique_pair {S Q : Finset ℤ} {s : ℤ}
    (hz : 0∈S) (hs : s∈S) (hs0 : s≠0) (hbad : ¬IsAP S)
    (hmin : ∀ y∈S, y≠0 → s.natAbs≤y.natAbs)
    (hunique : IntrinsicPairs 0 S={Q}) : s∈Q := by
  by_contra hn
  apply hbad
  apply minimum_spoke_closed_isAP hz hs hs0 hmin
  intro w hw
  apply completion_full_away_pair hz hunique hs hw
  intro he
  exact hn (he ▸ (show s∈({s,w} : Finset ℤ) by simp))

theorem completion_spoke_away_exception {S : Finset ℤ} {s v : ℤ}
    (hz : 0∈S) (hs : s∈S) (hsv : s≠v)
    (hunique : IntrinsicPairs 0 S={{s,v}}) {w : ℤ} (hw : w∈S) (hwv : w≠v) :
    ∀ x, Completion s w x → x∈S := by
  have hn : ({s,w} : Finset ℤ)≠{s,v} := by
    intro he
    have hv : v∈({s,w} : Finset ℤ) := he.symm ▸ (by simp : v∈({s,v} : Finset ℤ))
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with he | he
    · exact hsv he.symm
    · exact hwv he.symm
  exact completion_full_away_pair hz hunique hs hw hn

theorem minimum_dvd_away_exception {S : Finset ℤ} {s v : ℤ}
    (hz : 0∈S) (hs : s∈S) (hs0 : s≠0) (hsv : s≠v)
    (hmin : ∀ y∈S, y≠0 → s.natAbs≤y.natAbs)
    (hunique : IntrinsicPairs 0 S={{s,v}}) {w : ℤ} (hw : w∈S) (hwv : w≠v) : s∣w := by
  exact Int.gcd_eq_natAbs_left_iff_dvd.mp (minimum_abs_gcd_of_full_pair hs0 hmin
    (completion_spoke_away_exception hz hs hsv hunique hw hwv))

theorem dvd_of_le_dvd_double {m g : ℕ} (hm : 0<m) (hmg : m≤g) (hd : g∣2*m) : m∣g := by
  obtain ⟨q,hq⟩ := hd
  have hqpos : 0<q := by
    by_contra hn
    have hz : q=0 := by omega
    rw [hz,mul_zero] at hq
    omega
  have hqle : q≤2 := by
    by_contra hn
    have hq3 : 3≤q := by omega
    have hmul := Nat.mul_le_mul_right g hq3
    nlinarith
  have hcases : q=1 ∨ q=2 := by omega
  rcases hcases with rfl | rfl
  · refine ⟨2,?_⟩
    omega
  · have hg : g=m := by omega
    simp [hg]

theorem dvd_of_gcd_large_on_opposite_or_double {s a b : ℤ} (hs0 : s≠0)
    (ha : a=-s ∨ a=2*s) (hge : s.natAbs≤Int.gcd a b) : s∣b := by
  have hmd : s.natAbs∣Int.gcd a b := by
    rcases ha with rfl | rfl
    · have hle := Int.gcd_le_natAbs_left b (show -s≠0 by omega)
      have hle' : Int.gcd (-s) b≤s.natAbs := by simpa using hle
      have he : Int.gcd (-s) b=s.natAbs := Nat.le_antisymm hle' hge
      simp [he]
    · have hd : Int.gcd (2*s) b∣2*s.natAbs := by
        simpa [Int.natAbs_mul] using Int.gcd_dvd_natAbs_left (2*s) b
      exact dvd_of_le_dvd_double (Int.natAbs_pos.mpr hs0) hge hd
  apply Int.natAbs_dvd.mp
  exact dvd_trans (by exact_mod_cast hmd) (Int.gcd_dvd_right a b)

theorem opposite_or_double_in_singleton_set {S : Finset ℤ} {s v : ℤ}
    (hz : 0∈S) (hs : s∈S) (hs0 : s≠0) (hsv : s≠v) (hcard : 4≤S.card)
    (hmin : ∀ y∈S, y≠0 → s.natAbs≤y.natAbs)
    (hunique : IntrinsicPairs 0 S={{s,v}}) (hnot : ¬s∣v) :
    ∃ a∈S, a≠s ∧ a≠v ∧ (a=-s ∨ a=2*s) := by
  have hc3 : ({0,s,v} : Finset ℤ).card≤3 := Finset.card_le_three
  obtain ⟨w,hw,hwn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({0,s,v} : Finset ℤ).card<S.card by omega)
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hwn
  have hd := minimum_dvd_away_exception hz hs hs0 hsv hmin hunique hw hwn.2.2
  have hg := Int.gcd_eq_natAbs_left_iff_dvd.mpr hd
  have hfull := completion_spoke_away_exception hz hs hsv hunique hw hwn.2.2
  obtain ⟨k,hk⟩ := hd
  have hk0 : k≠0 := by intro he; rw [he,mul_zero] at hk; exact hwn.1 hk
  have hk1 : k≠1 := by intro he; rw [he,mul_one] at hk; exact hwn.2.1 hk
  have hnegv : -s≠v := by intro he; apply hnot; rw [←he]; exact dvd_neg.mpr (dvd_refl _)
  have hdblv : 2*s≠v := by
    intro he
    apply hnot
    rw [←he]
    exact ⟨2,by ring⟩
  have hkcases : k≤-1 ∨ 2≤k := by omega
  rcases hkcases with hkm | hkp
  · have hbounds : min 0 (min s w)≤-s ∧ -s≤max 0 (max s w) := by
      by_cases hsp : 0≤s
      · have hp := mul_nonneg (show 0≤-1-k by omega) hsp
        have hb : w≤-s := by nlinarith
        constructor <;> omega
      · have hp := mul_nonneg (show 0≤-1-k by omega) (show 0≤-s by omega)
        have hb : -s≤w := by nlinarith
        constructor <;> omega
    refine ⟨-s,hfull _ ⟨hbounds.1,hbounds.2,?_⟩,by omega,hnegv,Or.inl rfl⟩
    rw [hg]
    exact dvd_neg.mpr (Int.natAbs_dvd_self (a:=s))
  · have hbounds : min 0 (min s w)≤2*s ∧ 2*s≤max 0 (max s w) := by
      by_cases hsp : 0≤s
      · have hp := mul_nonneg (show 0≤k-2 by omega) hsp
        have hb : 2*s≤w := by nlinarith
        constructor <;> omega
      · have hp := mul_nonneg (show 0≤k-2 by omega) (show 0≤-s by omega)
        have hb : w≤2*s := by nlinarith
        constructor <;> omega
    refine ⟨2*s,hfull _ ⟨hbounds.1,hbounds.2,?_⟩,by omega,hdblv,Or.inr rfl⟩
    rw [hg]
    simpa only [mul_comm] using dvd_mul_of_dvd_left (Int.natAbs_dvd_self (a:=s)) (2:ℤ)

theorem minimum_dvd_all_singleton_set {S : Finset ℤ} {s v : ℤ}
    (hz : 0∈S) (hs : s∈S) (hv : v∈S) (hs0 : s≠0) (hsv : s≠v) (hcard : 4≤S.card)
    (hmin : ∀ y∈S, y≠0 → s.natAbs≤y.natAbs)
    (hunique : IntrinsicPairs 0 S={{s,v}}) : ∀ w∈S, s∣w := by
  have hvdiv : s∣v := by
    by_contra hn
    obtain ⟨a,ha,has,hav,hshape⟩ :=
      opposite_or_double_in_singleton_set hz hs hs0 hsv hcard hmin hunique hn
    have hpair : ({a,v} : Finset ℤ)≠{s,v} := by
      intro he
      have hm : s∈({a,v} : Finset ℤ) := he.symm ▸ (by simp : s∈({s,v} : Finset ℤ))
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with he | he
      · exact has he.symm
      · exact hsv he
    have ha0 : a≠0 := by rcases hshape with rfl | rfl <;> omega
    have hge := minimum_abs_le_gcd_of_full_pair hmin ha0
      (completion_full_away_pair hz hunique ha hv hpair)
    exact hn (dvd_of_gcd_large_on_opposite_or_double hs0 hshape hge)
  intro w hw
  by_cases he : w=v
  · simpa only [he] using hvdiv
  · exact minimum_dvd_away_exception hz hs hs0 hsv hmin hunique hw he

theorem exists_minimum_nonzero (S : Finset ℤ) (hcard : 2≤S.card) :
    ∃ s∈S, s≠0 ∧ ∀ y∈S, y≠0 → s.natAbs≤y.natAbs := by
  have hnon : ∃ s∈S, s≠0 := by
    by_contra hn
    have hsub : S⊆{0} := by
      intro s hs
      by_cases he : s=0
      · simp [he]
      · exact False.elim (hn ⟨s,hs,he⟩)
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  let A := (S.filter (fun x => x≠0)).image Int.natAbs
  have hA : A.Nonempty := by
    obtain ⟨x,hx,hx0⟩ := hnon
    exact ⟨x.natAbs,Finset.mem_image.mpr ⟨x,by simp [hx,hx0],rfl⟩⟩
  obtain ⟨s,hs',hsa⟩ := Finset.mem_image.mp (Finset.min'_mem A hA)
  obtain ⟨hs,hs0⟩ := Finset.mem_filter.mp hs'
  refine ⟨s,hs,hs0,?_⟩
  intro y hy hy0
  rw [hsa]
  exact Finset.min'_le A _ (Finset.mem_image.mpr ⟨y,by simp [hy,hy0],rfl⟩)

theorem pair_eq_at_member {Q : Finset ℤ} {s : ℤ} (hcard : Q.card=2) (hs : s∈Q) :
    ∃ v∈Q, s≠v ∧ Q={s,v} := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hcard
  simp only [Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact ⟨b,by simp,hab,rfl⟩
  · exact ⟨a,by simp,Ne.symm hab,Finset.pair_comm _ _⟩

def MinimumGridException (S : Finset ℤ) : Prop :=
  ∃ s∈S, s≠0 ∧ (∀ y∈S, y≠0 → s.natAbs≤y.natAbs) ∧
    ∃ v∈S, v≠0 ∧ s≠v ∧ IntrinsicPairs 0 S={{s,v}} ∧ ∀ w∈S, s∣w

theorem singleton_intrinsic_minimum_grid {S : Finset ℤ}
    (hz : 0∈S) (hbad : ¬IsAP S) (hcard : 4≤S.card)
    (hsingle : (IntrinsicPairs 0 S).card=1) : MinimumGridException S := by
  obtain ⟨s,hs,hs0,hmin⟩ := exists_minimum_nonzero S (by omega)
  obtain ⟨Q,hQeq⟩ := Finset.card_eq_one.mp hsingle
  have hQmem : Q∈IntrinsicPairs 0 S := by rw [hQeq]; simp
  obtain ⟨hQS,hQcard,hQ0,hQw⟩ := (mem_intrinsicPairs 0 S Q).mp hQmem
  have hsQ := minimum_mem_unique_pair hz hs hs0 hbad hmin hQeq
  obtain ⟨v,hvQ,hsv,hQsv⟩ := pair_eq_at_member hQcard hsQ
  have hv : v∈S := hQS hvQ
  have hv0 : v≠0 := by intro he; exact hQ0 (he ▸ hvQ)
  have hu : IntrinsicPairs 0 S={{s,v}} := by simpa only [hQsv] using hQeq
  exact ⟨s,hs,hs0,hmin,v,hv,hv0,hsv,hu,
    minimum_dvd_all_singleton_set hz hs hv hs0 hsv hcard hmin hu⟩

theorem actual_singleton_minimum_grid {Ω : Finset ℤ} {G : Finset (Finset ℤ)}
    (hlegal : Legal Ω G) (hroot : Rooted G 0) {S : Finset ℤ}
    (hS : S∈SingletonPrivateLarge 0 Ω G) : MinimumGridException S := by
  have hsingle := singletonPrivateLarge_intrinsic_card_one hlegal hroot hS
  obtain ⟨hlarge,hpool⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSG,hbad,hcard⟩ := Finset.mem_filter.mp hlarge
  exact singleton_intrinsic_minimum_grid (hroot S hSG) hbad hcard hsingle

theorem minimum_exception_interval {S : Finset ℤ} {s v : ℤ}
    (hz : 0∈S) (hs : s∈S) (hv : v∈S) (hs0 : s≠0) (hv0 : v≠0) (hsv : s≠v)
    (hbad : ¬IsAP S) (hunique : IntrinsicPairs 0 S={{s,v}})
    (hdiv : ∀ w∈S, s∣w) :
    ∃ lo hi : ℤ, lo≤0 ∧ 0≤hi ∧ (v<lo ∨ hi<v) ∧
      S.erase v=(Finset.Icc lo hi).filter (fun x => (s.natAbs : ℤ)∣x) ∧
      IsAP (S.erase v) := by
  let T := S.erase v
  have hzT : 0∈T := Finset.mem_erase.mpr ⟨Ne.symm hv0,hz⟩
  have hne : T.Nonempty := ⟨0,hzT⟩
  let lo := T.min' hne
  let hi := T.max' hne
  have hlo : lo∈T := Finset.min'_mem T hne
  have hhi : hi∈T := Finset.max'_mem T hne
  have hlo0 : lo≤0 := Finset.min'_le T 0 hzT
  have hhi0 : 0≤hi := Finset.le_max' T 0 hzT
  let H := (Finset.Icc lo hi).filter (fun x => (s.natAbs : ℤ)∣x)
  have hpos : 0<(s.natAbs : ℤ) := by have hh := Int.natAbs_pos.mpr hs0; omega
  have hHAP : IsAP H := by
    refine ⟨s.natAbs,0,hpos,lo,hi,?_,?_⟩
    · intro x
      simp only [H,Finset.mem_filter,Finset.mem_Icc,sub_zero,and_assoc]
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo0,hhi0⟩,dvd_zero _⟩
  have hTH : T⊆H := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Finset.min'_le T x hx,Finset.le_max' T x hx⟩,
      Int.natAbs_dvd.mpr (hdiv x (Finset.mem_erase.mp hx).2)⟩
  have hHS : H⊆S := by
    intro x hx
    obtain ⟨hb,hd⟩ := Finset.mem_filter.mp hx
    obtain ⟨hlox,hxhi⟩ := Finset.mem_Icc.mp hb
    by_cases hx0 : 0≤x
    · have hhiS : hi∈S := (Finset.mem_erase.mp hhi).2
      have hhin : hi≠v := (Finset.mem_erase.mp hhi).1
      have hg := Int.gcd_eq_natAbs_left_iff_dvd.mpr (hdiv hi hhiS)
      apply completion_spoke_away_exception hz hs hsv hunique hhiS hhin x
      exact ⟨by omega,by omega,by simpa only [hg] using hd⟩
    · have hloS : lo∈S := (Finset.mem_erase.mp hlo).2
      have hlon : lo≠v := (Finset.mem_erase.mp hlo).1
      have hg := Int.gcd_eq_natAbs_left_iff_dvd.mpr (hdiv lo hloS)
      apply completion_spoke_away_exception hz hs hsv hunique hloS hlon x
      exact ⟨by omega,by omega,by simpa only [hg] using hd⟩
  have hvn : v∉H := by
    intro hvH
    have hSH : S⊆H := by
      intro x hx
      by_cases he : x=v
      · simpa only [he] using hvH
      · exact hTH (Finset.mem_erase.mpr ⟨he,hx⟩)
    exact hbad (by rw [Finset.Subset.antisymm hSH hHS]; exact hHAP)
  have hHT : H⊆T := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_,hHS hx⟩
    intro he
    exact hvn (he ▸ hx)
  have hTeq : T=H := Finset.Subset.antisymm hTH hHT
  have hvout : v<lo ∨ hi<v := by
    by_contra hn
    apply hvn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,
      Int.natAbs_dvd.mpr (hdiv v hv)⟩
  exact ⟨lo,hi,hlo0,hhi0,hvout,hTeq,by rw [show S.erase v=H from hTeq]; exact hHAP⟩

theorem singleton_intrinsic_isAP_erase {S : Finset ℤ}
    (hz : 0∈S) (hbad : ¬IsAP S) (hcard : 4≤S.card)
    (hsingle : (IntrinsicPairs 0 S).card=1) :
    ∃ v∈S, v≠0 ∧ IsAP (S.erase v) := by
  obtain ⟨s,hs,hs0,hmin,v,hv,hv0,hsv,hu,hd⟩ :=
    singleton_intrinsic_minimum_grid hz hbad hcard hsingle
  obtain ⟨lo,hi,hlo,hhi,hout,heq,hAP⟩ :=
    minimum_exception_interval hz hs hv hs0 hv0 hsv hbad hu hd
  exact ⟨v,hv,hv0,hAP⟩

theorem actual_singleton_isAP_erase {Ω : Finset ℤ} {G : Finset (Finset ℤ)}
    (hlegal : Legal Ω G) (hroot : Rooted G 0) {S : Finset ℤ}
    (hS : S∈SingletonPrivateLarge 0 Ω G) : ∃ v∈S, v≠0 ∧ IsAP (S.erase v) := by
  have hsingle := singletonPrivateLarge_intrinsic_card_one hlegal hroot hS
  obtain ⟨hlarge,hpool⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSG,hbad,hcard⟩ := Finset.mem_filter.mp hlarge
  exact singleton_intrinsic_isAP_erase (hroot S hSG) hbad hcard hsingle

theorem affine_injective_of_ne_zero (c d : ℤ) (hd : d≠0) :
    Function.Injective (affine c d) := by
  intro x y hxy
  have hh : d*x=d*y := by dsimp [affine] at hxy; omega
  exact mul_left_cancel₀ hd hh

theorem mem_mapSet_of_ne_zero (c d : ℤ) (hd : d≠0) (S : Finset ℤ) (x : ℤ) :
    affine c d x∈mapSet c d S ↔ x∈S := by
  constructor
  · intro hx
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hx
    simpa only [affine_injective_of_ne_zero c d hd heq] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem mapSet_injective_of_ne_zero (c d : ℤ) (hd : d≠0) :
    Function.Injective (mapSet c d) := by
  intro S T hST
  ext x
  rw [←mem_mapSet_of_ne_zero c d hd S x,←mem_mapSet_of_ne_zero c d hd T x,hST]

theorem mapSet_card_of_ne_zero (c d : ℤ) (hd : d≠0) (S : Finset ℤ) :
    (mapSet c d S).card=S.card :=
  Finset.card_image_of_injective S (affine_injective_of_ne_zero c d hd)

theorem completion_scale_iff (d u v x : ℤ) (hd : d≠0) :
    Completion (d*u) (d*v) (d*x) ↔ Completion u v x := by
  have hdiv : (Int.gcd (d*u) (d*v) : ℤ)∣d*x ↔ (Int.gcd u v : ℤ)∣x := by
    simp only [Int.gcd_mul_left,Int.ofNat_dvd_left,Int.natAbs_mul]
    exact Nat.mul_dvd_mul_iff_left (Int.natAbs_pos.mpr hd)
  by_cases hp : 0<d
  · have hm : Monotone (fun z : ℤ => d*z) := fun a b hab => mul_le_mul_of_nonneg_left hab hp.le
    have hmin : d*min 0 (min u v)=min 0 (min (d*u) (d*v)) := by
      calc
        _=min (d*0) (d*min u v) := hm.map_min
        _=_ := by rw [mul_zero,show d*min u v=min (d*u) (d*v) from hm.map_min]
    have hmax : d*max 0 (max u v)=max 0 (max (d*u) (d*v)) := by
      calc
        _=max (d*0) (d*max u v) := hm.map_max
        _=_ := by rw [mul_zero,show d*max u v=max (d*u) (d*v) from hm.map_max]
    simp only [Completion,←hmin,←hmax,Int.mul_le_mul_left hp,hdiv]
  · have hn : d<0 := by omega
    have hm : Antitone (fun z : ℤ => d*z) := fun a b hab => mul_le_mul_of_nonpos_left hab hn.le
    have hmin : d*max 0 (max u v)=min 0 (min (d*u) (d*v)) := by
      calc
        _=min (d*0) (d*max u v) := hm.map_max
        _=_ := by rw [mul_zero,show d*max u v=min (d*u) (d*v) from hm.map_max]
    have hmax : d*min 0 (min u v)=max 0 (max (d*u) (d*v)) := by
      calc
        _=max (d*0) (d*min u v) := hm.map_min
        _=_ := by rw [mul_zero,show d*min u v=max (d*u) (d*v) from hm.map_min]
    simp only [Completion,←hmin,←hmax,mul_le_mul_left_of_neg hn,hdiv]
    constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨h2,h1,h3⟩

theorem completionAt_affine_iff (c d u v x : ℤ) (hd : d≠0) :
    CompletionAt c (affine c d u) (affine c d v) (affine c d x) ↔ Completion u v x := by
  have hu : affine c d u-c=d*u := by dsimp [affine]; ring
  have hv : affine c d v-c=d*v := by dsimp [affine]; ring
  have hx : affine c d x-c=d*x := by dsimp [affine]; ring
  rw [CompletionAt,hu,hv,hx]
  exact completion_scale_iff d u v x hd

theorem intrinsicPairs_map_subset (c d : ℤ) (hd : d≠0) (S : Finset ℤ) :
    (IntrinsicPairs 0 S).image (mapSet c d) ⊆ IntrinsicPairs c (mapSet c d S) := by
  intro P hP
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨hsub,hcard,hroot,u,hu,v,hv,x,hx,hxn⟩ := (mem_intrinsicPairs 0 S Q).mp hQ
  apply (mem_intrinsicPairs c (mapSet c d S) (mapSet c d Q)).mpr
  refine ⟨Finset.image_subset_image hsub,?_,?_,affine c d u,
    Finset.mem_image.mpr ⟨u,hu,rfl⟩,affine c d v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,
    affine c d x,?_,?_⟩
  · rw [mapSet_card_of_ne_zero c d hd,hcard]
  · intro hcQ
    have hh : affine c d 0∈mapSet c d Q := by simpa only [affine_zero] using hcQ
    exact hroot ((mem_mapSet_of_ne_zero c d hd Q 0).mp hh)
  · exact (completionAt_affine_iff c d u v x hd).mpr
      (by simpa only [CompletionAt,sub_zero] using hx)
  · intro hmem
    exact hxn ((mem_mapSet_of_ne_zero c d hd S x).mp hmem)

theorem intrinsicPairs_card_map_le (c d : ℤ) (hd : d≠0) (S : Finset ℤ) :
    (IntrinsicPairs 0 S).card≤(IntrinsicPairs c (mapSet c d S)).card := by
  have hc : ((IntrinsicPairs 0 S).image (mapSet c d)).card=(IntrinsicPairs 0 S).card :=
    Finset.card_image_of_injective _ (mapSet_injective_of_ne_zero c d hd)
  rw [←hc]
  exact Finset.card_le_card (intrinsicPairs_map_subset c d hd S)

def Negated (S : Finset ℤ) : Finset ℤ := S.image (fun x => -x)

theorem mem_negated (S : Finset ℤ) (x : ℤ) : x∈Negated S ↔ -x∈S := by
  constructor
  · intro hx
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hx
    have hh : -x=y := by omega
    simpa only [hh] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨-x,hx,by simp⟩

theorem negated_isAP {S : Finset ℤ} (hS : IsAP S) : IsAP (Negated S) := by
  obtain ⟨d,p,hd,lo,hi,hrep,hp⟩ := hS
  refine ⟨d,-p,hd,-hi,-lo,?_,?_⟩
  · intro x
    rw [mem_negated,hrep]
    have he : -x-p=-(x-(-p)) := by ring
    rw [he,dvd_neg]
    constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨by omega,by omega,h3⟩
  · apply (mem_negated S (-p)).mpr
    simpa using hp

theorem affine_isAP_of_ne_zero (c d : ℤ) (hd : d≠0) {S : Finset ℤ}
    (hS : IsAP S) : IsAP (mapSet c d S) := by
  by_cases hp : 0<d
  · exact AffineLine30.affine_isAP c d hp hS
  · have hn : 0< -d := by omega
    have he : mapSet c d S=mapSet c (-d) (Negated S) := by
      unfold mapSet Negated
      rw [Finset.image_image]
      apply Finset.image_congr
      intro x hx
      dsimp [Function.comp,affine]
      ring
    rw [he]
    exact AffineLine30.affine_isAP c (-d) hn (negated_isAP hS)

theorem shift_inverse_mapSet (c : ℤ) (S : Finset ℤ) : mapSet c 1 (Shift S c)=S := by
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hx
    have hh := mem_shift_iff.mp hy
    have he : y+c=x := by dsimp [affine] at heq; omega
    simpa only [he] using hh
  · intro hx
    exact Finset.mem_image.mpr ⟨x-c,mem_shift_iff.mpr (by simpa using hx),by dsimp [affine]; ring⟩

theorem shift_card (c : ℤ) (S : Finset ℤ) : (Shift S c).card=S.card := by
  apply Finset.card_image_of_injective
  intro x y he
  dsimp at he
  omega

theorem mapSet_translate_scale (c s : ℤ) (S : Finset ℤ) :
    mapSet c 1 (mapSet 0 s S)=mapSet c s S := by
  unfold mapSet
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x hx
  dsimp [Function.comp,affine]
  ring

theorem singleton_intrinsic_unit_normalization {S : Finset ℤ}
    (hz : 0∈S) (hbad : ¬IsAP S) (hcard : 4≤S.card)
    (hsingle : (IntrinsicPairs 0 S).card=1) :
    ∃ s : ℤ, ∃ U : Finset ℤ, s≠0 ∧ mapSet 0 s U=S ∧ 0∈U ∧ 1∈U ∧
      4≤U.card ∧ ¬IsAP U ∧ (IntrinsicPairs 0 U).card=1 := by
  obtain ⟨s,hs,hs0,hmin,v,hv,hv0,hsv,hu,hdiv⟩ :=
    singleton_intrinsic_minimum_grid hz hbad hcard hsingle
  let U := S.image (fun x => x/s)
  have hmap : mapSet 0 s U=S := by
    change (S.image (fun x => x/s)).image (affine 0 s)=S
    rw [Finset.image_image]
    calc
      S.image ((affine 0 s) ∘ (fun x => x/s))=S.image id := by
        apply Finset.image_congr
        intro x hx
        dsimp [Function.comp,affine]
        simpa only [zero_add] using Int.mul_ediv_cancel_of_dvd (hdiv x hx)
      _=S := Finset.image_id
  have hzU : 0∈U := Finset.mem_image.mpr ⟨0,hz,by simp⟩
  have h1U : 1∈U := Finset.mem_image.mpr ⟨s,hs,by simp [Int.ediv_self hs0]⟩
  have hcU : U.card=S.card := by
    calc
      U.card=(mapSet 0 s U).card := (mapSet_card_of_ne_zero 0 s hs0 U).symm
      _=S.card := congrArg Finset.card hmap
  have hbU : ¬IsAP U := by
    intro hAP
    exact hbad (by rw [←hmap]; exact affine_isAP_of_ne_zero 0 s hs0 hAP)
  have hpU := Finset.card_pos.mpr (intrinsicPairs_nonempty hzU hbU)
  have hlU := intrinsicPairs_card_map_le 0 s hs0 U
  rw [hmap,hsingle] at hlU
  exact ⟨s,U,hs0,hmap,hzU,h1U,by omega,hbU,by omega⟩

theorem unit_singleton_exception {U : Finset ℤ} (hz : 0∈U) (h1 : 1∈U)
    (hbad : ¬IsAP U) (hsingle : (IntrinsicPairs 0 U).card=1) :
    ∃ v∈U, v≠0 ∧ 1≠v ∧ IntrinsicPairs 0 U={{1,v}} := by
  obtain ⟨Q,hQeq⟩ := Finset.card_eq_one.mp hsingle
  have hQmem : Q∈IntrinsicPairs 0 U := by rw [hQeq]; simp
  obtain ⟨hQU,hQcard,hQ0,hQw⟩ := (mem_intrinsicPairs 0 U Q).mp hQmem
  have hmin : ∀ y∈U, y≠0 → (1:ℤ).natAbs≤y.natAbs := by
    intro y hy hy0
    have hp := Int.natAbs_pos.mpr hy0
    change 1≤y.natAbs
    omega
  have h1Q := minimum_mem_unique_pair hz h1 (by decide) hbad hmin hQeq
  obtain ⟨v,hvQ,h1v,hQv⟩ := pair_eq_at_member hQcard h1Q
  exact ⟨v,hQU hvQ,by intro he; exact hQ0 (he ▸ hvQ),h1v,by simpa only [hQv] using hQeq⟩

theorem singleton_intrinsic_at_unit_normalization {c : ℤ} {S : Finset ℤ}
    (hc : c∈S) (hbad : ¬IsAP S) (hcard : 4≤S.card)
    (hsingle : (IntrinsicPairs c S).card=1) :
    ∃ s : ℤ, ∃ U : Finset ℤ, ∃ v : ℤ,
      s≠0 ∧ S=mapSet c s U ∧ 0∈U ∧ 1∈U ∧ 4≤U.card ∧ ¬IsAP U ∧
      v∈U ∧ v≠0 ∧ 1≠v ∧ IntrinsicPairs 0 U={{1,v}} := by
  let V := Shift S c
  have h0V : 0∈V := mem_shift_iff.mpr (by simpa using hc)
  have hbV : ¬IsAP V := fun hAP => hbad ((isAP_shift_iff S c).mp hAP)
  have hcV : 4≤V.card := by rw [show V.card=S.card from shift_card c S]; exact hcard
  have hVmap : mapSet c 1 V=S := shift_inverse_mapSet c S
  have hpV := Finset.card_pos.mpr (intrinsicPairs_nonempty h0V hbV)
  have hlV := intrinsicPairs_card_map_le c 1 (by decide) V
  rw [hVmap,hsingle] at hlV
  obtain ⟨s,U,hs0,hU,h0U,h1U,hcU,hbU,hpU⟩ :=
    singleton_intrinsic_unit_normalization h0V hbV hcV (by omega)
  obtain ⟨v,hv,hv0,h1v,hUv⟩ := unit_singleton_exception h0U h1U hbU hpU
  refine ⟨s,U,v,hs0,?_,h0U,h1U,hcU,hbU,hv,hv0,h1v,hUv⟩
  calc
    S=mapSet c 1 V := hVmap.symm
    _=mapSet c 1 (mapSet 0 s U) := by rw [hU]
    _=mapSet c s U := mapSet_translate_scale c s U

theorem actual_singleton_unit_normalization {c : ℤ} {Ω : Finset ℤ}
    {G : Finset (Finset ℤ)} (hlegal : Legal Ω G) (hroot : Rooted G c)
    {S : Finset ℤ} (hS : S∈SingletonPrivateLarge c Ω G) :
    ∃ s : ℤ, ∃ U : Finset ℤ, ∃ v : ℤ,
      s≠0 ∧ S=mapSet c s U ∧ 0∈U ∧ 1∈U ∧ 4≤U.card ∧ ¬IsAP U ∧
      v∈U ∧ v≠0 ∧ 1≠v ∧ IntrinsicPairs 0 U={{1,v}} := by
  have hsingle := singletonPrivateLarge_intrinsic_card_one hlegal hroot hS
  obtain ⟨hlarge,hpool⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSG,hbad,hcard⟩ := Finset.mem_filter.mp hlarge
  exact singleton_intrinsic_at_unit_normalization (hroot S hSG) hbad hcard hsingle

#print axioms mem_intrinsicPairs
#print axioms missing_pair_properties
#print axioms pair_mem_intrinsicPairs
#print axioms intrinsicPairs_nonempty
#print axioms intrinsic_pair_not_isAP
#print axioms intrinsic_pair_private
#print axioms intrinsicPairs_subset_privatePool
#print axioms intrinsicPairs_card_one_of_privatePool
#print axioms singletonPrivateLarge_intrinsic_card_one
#print axioms completion_full_away_pair
#print axioms minimum_abs_le_gcd_of_full_pair
#print axioms minimum_abs_gcd_of_full_pair
#print axioms minimum_spoke_closed_isAP
#print axioms minimum_mem_unique_pair
#print axioms completion_spoke_away_exception
#print axioms minimum_dvd_away_exception
#print axioms dvd_of_le_dvd_double
#print axioms dvd_of_gcd_large_on_opposite_or_double
#print axioms opposite_or_double_in_singleton_set
#print axioms minimum_dvd_all_singleton_set
#print axioms exists_minimum_nonzero
#print axioms pair_eq_at_member
#print axioms singleton_intrinsic_minimum_grid
#print axioms actual_singleton_minimum_grid
#print axioms minimum_exception_interval
#print axioms singleton_intrinsic_isAP_erase
#print axioms actual_singleton_isAP_erase
#print axioms affine_injective_of_ne_zero
#print axioms mem_mapSet_of_ne_zero
#print axioms mapSet_injective_of_ne_zero
#print axioms mapSet_card_of_ne_zero
#print axioms completion_scale_iff
#print axioms completionAt_affine_iff
#print axioms intrinsicPairs_map_subset
#print axioms intrinsicPairs_card_map_le
#print axioms mem_negated
#print axioms negated_isAP
#print axioms affine_isAP_of_ne_zero
#print axioms shift_inverse_mapSet
#print axioms shift_card
#print axioms mapSet_translate_scale
#print axioms singleton_intrinsic_unit_normalization
#print axioms unit_singleton_exception
#print axioms singleton_intrinsic_at_unit_normalization
#print axioms actual_singleton_unit_normalization
end
end JSP233.SinglePrivate32
