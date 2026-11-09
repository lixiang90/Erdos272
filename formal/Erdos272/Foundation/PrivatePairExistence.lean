module

public import Erdos272.Foundation.StarCompletion
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Ring.Divisibility.Basic

@[expose] public section

/-!
Intrinsic private-pair existence for actual finite integer sets.  In contrast
with an interface that assumes a missing completion, `missing_completion_exists`
constructs one from non-arithmeticity alone.  The star cardinality theorem is
not used.  Completion is the smallest AP containing 0, u and v.
-/

namespace JSP233.PrivatePairExistence

open StarCompletion

def Completion (u v x : Int) : Prop :=
  min 0 (min u v) ≤ x ∧ x ≤ max 0 (max u v) ∧ (Int.gcd u v : Int) ∣ x

theorem completion_least {S : Finset Int} (hS : IsAP S)
    {u v : Int} (hz : 0 ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    {x : Int} (hx : Completion u v x) : x ∈ S := by
  obtain ⟨d, p, hd, lo, hi, hrep, hp⟩ := hS
  have hz' := (hrep 0).mp hz
  have hu' := (hrep u).mp hu
  have hv' := (hrep v).mp hv
  have hdu : d ∣ u := by simpa using dvd_sub hu'.2.2 hz'.2.2
  have hdv : d ∣ v := by simpa using dvd_sub hv'.2.2 hz'.2.2
  have hg : d ∣ (Int.gcd u v : Int) := Int.dvd_coe_gcd hdu hdv
  apply (hrep x).mpr
  refine ⟨by have := hx.1; omega, by have := hx.2.1; omega, ?_⟩
  have hdx := dvd_trans hg hx.2.2
  convert Int.dvd_add hdx hz'.2.2 using 1; omega

def CompletionClosed (S : Finset Int) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ∀ x, Completion u v x → x ∈ S

theorem minimum_abs_gcd {S : Finset Int} (hcl : CompletionClosed S)
    {s : Int} (hs : s ∈ S) (hs0 : s ≠ 0)
    (hmin : ∀ y ∈ S, y ≠ 0 → s.natAbs ≤ y.natAbs) (w : Int) (hw : w ∈ S) :
    Int.gcd s w = s.natAbs := by
  have hp : 0 < Int.gcd s w := Int.gcd_pos_of_ne_zero_left w hs0
  have hle : Int.gcd s w ≤ s.natAbs := Int.gcd_le_natAbs_left w hs0
  by_cases hspos : 0 ≤ s
  · have hsg : (s.natAbs : Int) = s := Int.natAbs_of_nonneg hspos
    have hc : Completion s w (Int.gcd s w : Int) := by
      refine ⟨by omega, by omega, dvd_refl _⟩
    have hmem := hcl s hs w hw _ hc
    have hge := hmin _ hmem (by omega)
    simpa using Nat.le_antisymm hle hge
  · have hsg : (s.natAbs : Int) = -s := by
      simpa using Int.natAbs_of_nonneg (show 0 ≤ -s by omega)
    have hc : Completion s w (-(Int.gcd s w : Int)) := by
      refine ⟨by omega, by omega, ?_⟩
      exact dvd_neg.mpr (dvd_refl _)
    have hmem := hcl s hs w hw _ hc
    have hge := hmin _ hmem (by omega)
    simpa using Nat.le_antisymm hle (by simpa using hge)

theorem closed_isAP {S : Finset Int} (hz : 0 ∈ S) (hcl : CompletionClosed S) :
    IsAP S := by
  classical
  by_cases hnon : ∃ x ∈ S, x ≠ 0
  · obtain ⟨s, hs, hs0, hmin⟩ : ∃ s ∈ S, s ≠ 0 ∧
        ∀ y ∈ S, y ≠ 0 → s.natAbs ≤ y.natAbs := by
      let A := (S.filter (fun x => x ≠ 0)).image Int.natAbs
      have hA : A.Nonempty := by
        obtain ⟨x, hx, hx0⟩ := hnon
        exact ⟨x.natAbs, Finset.mem_image.mpr ⟨x, by simp [hx, hx0], rfl⟩⟩
      obtain ⟨s, hs', hsa⟩ := Finset.mem_image.mp (Finset.min'_mem A hA)
      have hs := (Finset.mem_filter.mp hs').1
      have hs0 := (Finset.mem_filter.mp hs').2
      refine ⟨s, hs, hs0, ?_⟩
      intro y hy hy0
      rw [hsa]
      exact Finset.min'_le A _ (Finset.mem_image.mpr ⟨y, by simp [hy, hy0], rfl⟩)
    have hne : S.Nonempty := ⟨0, hz⟩
    let lo := S.min' hne
    let hi := S.max' hne
    have hlo : lo ∈ S := Finset.min'_mem S hne
    have hhi : hi ∈ S := Finset.max'_mem S hne
    have hgz : 0 < (s.natAbs : Int) := by have := Int.natAbs_pos.mpr hs0; omega
    refine ⟨s.natAbs, 0, hgz, lo, hi, ?_, hz⟩
    intro x
    constructor
    · intro hx
      refine ⟨Finset.min'_le S x hx, Finset.le_max' S x hx, ?_⟩
      have hg := minimum_abs_gcd hcl hs hs0 hmin x hx
      simpa [hg] using Int.gcd_dvd_right s x
    · intro hx
      have hlo0 : lo ≤ 0 := Finset.min'_le S 0 hz
      have hhi0 : 0 ≤ hi := Finset.le_max' S 0 hz
      by_cases hx0 : 0 ≤ x
      · apply hcl s hs hi hhi x
        refine ⟨by omega, by omega, ?_⟩
        simpa [minimum_abs_gcd hcl hs hs0 hmin hi hhi] using hx.2.2
      · apply hcl s hs lo hlo x
        refine ⟨by omega, by omega, ?_⟩
        simpa [minimum_abs_gcd hcl hs hs0 hmin lo hlo] using hx.2.2
  · have heq : S = {0} := by ext x; simp only [Finset.mem_singleton]; aesop
    rw [heq]
    exact singleton_isAP 0

theorem missing_completion_exists {S : Finset Int} (hz : 0 ∈ S) (hS : ¬ IsAP S) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧
      (∃ x, Completion u v x ∧ x ∉ S) ∧ ¬ IsAP ({0,u,v} : Finset Int) := by
  classical
  have hnot : ¬ CompletionClosed S := fun hcl => hS (closed_isAP hz hcl)
  simp only [CompletionClosed] at hnot
  push Not at hnot
  obtain ⟨u, hu, v, hv, x, hx, hxn⟩ := hnot
  have hbad : ¬ IsAP ({0,u,v} : Finset Int) := by
    intro hap
    have hmem := completion_least hap (by simp) (by simp) (by simp) hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl <;> contradiction
  have hu0 : u ≠ 0 := by
    intro hu0; subst u
    exact hbad (by simpa using pair_isAP 0 v)
  have hv0 : v ≠ 0 := by
    intro hv0; subst v
    exact hbad (by simpa [Finset.insert_comm, Finset.pair_comm] using pair_isAP 0 u)
  have huv : u ≠ v := by
    intro huv; subst v
    exact hbad (by simpa using pair_isAP 0 u)
  exact ⟨u, hu, v, hv, hu0, hv0, huv, ⟨x, hx, hxn⟩, hbad⟩

/-- The witness really is private in any legal rooted family: no other
member, whether arithmetic or crooked, contains both endpoints. -/
theorem private_pair_exists {Ω : Finset Int} {F : Finset (Finset Int)}
    (hlegal : Legal Ω F) (hroot : Rooted F 0)
    {S : Finset Int} (hSF : S ∈ F) (hS : ¬ IsAP S) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧
      ¬ IsAP ({0,u,v} : Finset Int) ∧
      ∀ T ∈ F, T ≠ S → ¬ (u ∈ T ∧ v ∈ T) := by
  obtain ⟨u, hu, v, hv, hu0, hv0, huv, ⟨x, hx, hxn⟩, hbad⟩ :=
    missing_completion_exists (hroot S hSF) hS
  refine ⟨u, hu, v, hv, hu0, hv0, huv, hbad, ?_⟩
  intro T hTF hTS hpair
  have hinter : IsAP (S ∩ T) := hlegal.2 S hSF T hTF hTS.symm
  apply hxn
  exact (Finset.mem_inter.mp (completion_least hinter
    (Finset.mem_inter.mpr ⟨hroot S hSF, hroot T hTF⟩)
    (Finset.mem_inter.mpr ⟨hu, hpair.1⟩)
    (Finset.mem_inter.mpr ⟨hv, hpair.2⟩) hx)).1

/-- Actual two-element resource sets, excluding every pair already contained
in an AP member of the original family.  No gcd-class counting bound is assumed. -/
noncomputable def AvailableBadPairs (Ω : Finset Int) (F : Finset (Finset Int)) :
    Finset (Finset Int) := by
  classical
  exact Ω.powerset.filter (fun Q => Q.card = 2 ∧ 0 ∉ Q ∧
    ¬ IsAP (insert 0 Q) ∧ ∀ T ∈ F, IsAP T → ¬ Q ⊆ T)

noncomputable def CrookedMembers (F : Finset (Finset Int)) : Finset (Finset Int) := by
  classical
  exact F.filter (fun S => ¬ IsAP S)

theorem private_resource_exists {Ω : Finset Int} {F : Finset (Finset Int)}
    (hlegal : Legal Ω F) (hroot : Rooted F 0)
    {S : Finset Int} (hSF : S ∈ F) (hS : ¬ IsAP S) :
    ∃ Q ∈ AvailableBadPairs Ω F, Q ⊆ S ∧
      ∀ T ∈ F, T ≠ S → ¬ Q ⊆ T := by
  classical
  obtain ⟨u, hu, v, hv, hu0, hv0, huv, hbad, hprivate⟩ :=
    private_pair_exists hlegal hroot hSF hS
  have hsub : ({u,v} : Finset Int) ⊆ S :=
    Finset.insert_subset_iff.mpr ⟨hu, Finset.singleton_subset_iff.mpr hv⟩
  have hp : ∀ T ∈ F, T ≠ S → ¬ ({u,v} : Finset Int) ⊆ T := by
    intro T hTF hTS hQT
    exact hprivate T hTF hTS ⟨hQT (by simp), hQT (by simp)⟩
  refine ⟨{u,v}, ?_, hsub, hp⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr (hsub.trans (hlegal.1 S hSF)), ?_⟩
  refine ⟨by simp [huv], by simp [Ne.symm hu0, Ne.symm hv0], hbad, ?_⟩
  intro T hTF hT
  by_cases hTS : T = S
  · subst T
    exact (hS hT).elim
  · exact hp T hTF hTS

/-- Every crooked member pays with a different actual bad pair outside all
AP-member pools.  This is an unconditional component of the star proof. -/
theorem crooked_members_card_le_available_pairs
    {Ω : Finset Int} {F : Finset (Finset Int)}
    (hlegal : Legal Ω F) (hroot : Rooted F 0) :
    (CrookedMembers F).card ≤ (AvailableBadPairs Ω F).card := by
  classical
  have hex : ∀ S : CrookedMembers F, ∃ Q : AvailableBadPairs Ω F,
      Q.val ⊆ S.val ∧ ∀ T ∈ F, T ≠ S.val → ¬ Q.val ⊆ T := by
    intro S
    have hS := Finset.mem_filter.mp S.property
    obtain ⟨Q, hQ, hsub, hp⟩ := private_resource_exists hlegal hroot hS.1 hS.2
    exact ⟨⟨Q, hQ⟩, hsub, hp⟩
  choose f hf using hex
  apply Finset.card_le_card_of_injective (f := f)
  intro S T hST
  apply Subtype.ext
  by_contra hne
  have hTF := (Finset.mem_filter.mp T.property).1
  have hnot := (hf S).2 T.val hTF (Ne.symm hne)
  apply hnot
  rw [show (f S).val = (f T).val from congrArg Subtype.val hST]
  exact (hf T).1

def Shift (S : Finset Int) (c : Int) : Finset Int := S.image (fun x => x-c)

theorem mem_shift_iff {S : Finset Int} {c x : Int} :
    x ∈ Shift S c ↔ x+c ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    have he' : x+c = y := by omega
    simpa [he'] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x+c, hx, by omega⟩

theorem isAP_shift_iff (S : Finset Int) (c : Int) : IsAP (Shift S c) ↔ IsAP S := by
  constructor
  · intro h
    obtain ⟨d, p, hd, lo, hi, hrep, hp⟩ := h
    refine ⟨d, p+c, hd, lo+c, hi+c, ?_, mem_shift_iff.mp hp⟩
    intro x
    have hm : x-c ∈ Shift S c ↔ x ∈ S := by simpa using
      (mem_shift_iff (S := S) (c := c) (x := x-c))
    rw [← hm, hrep]
    have he : x-c-p = x-(p+c) := by omega
    rw [he]
    omega
  · intro h
    obtain ⟨d, p, hd, lo, hi, hrep, hp⟩ := h
    refine ⟨d, p-c, hd, lo-c, hi-c, ?_, ?_⟩
    · intro x
      rw [mem_shift_iff, hrep]
      have he : x+c-p = x-(p-c) := by omega
      rw [he]
      omega
    · apply mem_shift_iff.mpr
      simpa using hp

def CompletionAt (c u v x : Int) : Prop := Completion (u-c) (v-c) (x-c)

theorem completionAt_least {S : Finset Int} (hS : IsAP S)
    {c u v : Int} (hc : c ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    {x : Int} (hx : CompletionAt c u v x) : x ∈ S := by
  have hz : 0 ∈ Shift S c := mem_shift_iff.mpr (by simpa using hc)
  have hu' : u-c ∈ Shift S c := mem_shift_iff.mpr (by simpa using hu)
  have hv' : v-c ∈ Shift S c := mem_shift_iff.mpr (by simpa using hv)
  have hm := completion_least ((isAP_shift_iff S c).mpr hS) hz hu' hv' hx
  simpa using mem_shift_iff.mp hm

theorem missing_completion_at_root_exists {S : Finset Int} {c : Int}
    (hc : c ∈ S) (hS : ¬ IsAP S) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ c ∧ v ≠ c ∧ u ≠ v ∧
      (∃ x, CompletionAt c u v x ∧ x ∉ S) ∧ ¬ IsAP ({c,u,v} : Finset Int) := by
  have hz : 0 ∈ Shift S c := mem_shift_iff.mpr (by simpa using hc)
  have hshift : ¬ IsAP (Shift S c) := fun h => hS ((isAP_shift_iff S c).mp h)
  obtain ⟨u, hu, v, hv, hu0, hv0, huv, ⟨x, hx, hxn⟩, hbad⟩ :=
    missing_completion_exists hz hshift
  have huS := mem_shift_iff.mp hu
  have hvS := mem_shift_iff.mp hv
  have hxnS : x+c ∉ S := fun hm => hxn (mem_shift_iff.mpr hm)
  refine ⟨u+c, huS, v+c, hvS, by omega, by omega, by omega,
    ⟨x+c, ?_, hxnS⟩, ?_⟩
  · simpa [CompletionAt] using hx
  · intro hap
    have hm := completionAt_least hap (by simp) (by simp) (by simp)
      (show CompletionAt c (u+c) (v+c) (x+c) by simpa [CompletionAt] using hx)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · apply hxnS; rw [hm]; exact hc
    · apply hxnS; rw [hm]; exact huS
    · apply hxnS; rw [hm]; exact hvS

theorem private_pair_at_root_exists {Ω : Finset Int} {F : Finset (Finset Int)}
    {c : Int} (hlegal : Legal Ω F) (hroot : Rooted F c)
    {S : Finset Int} (hSF : S ∈ F) (hS : ¬ IsAP S) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ c ∧ v ≠ c ∧ u ≠ v ∧
      ¬ IsAP ({c,u,v} : Finset Int) ∧
      ∀ T ∈ F, T ≠ S → ¬ (u ∈ T ∧ v ∈ T) := by
  obtain ⟨u, hu, v, hv, huc, hvc, huv, ⟨x, hx, hxn⟩, hbad⟩ :=
    missing_completion_at_root_exists (hroot S hSF) hS
  refine ⟨u, hu, v, hv, huc, hvc, huv, hbad, ?_⟩
  intro T hTF hTS hpair
  have hinter : IsAP (S ∩ T) := hlegal.2 S hSF T hTF hTS.symm
  apply hxn
  exact (Finset.mem_inter.mp (completionAt_least hinter
    (Finset.mem_inter.mpr ⟨hroot S hSF, hroot T hTF⟩)
    (Finset.mem_inter.mpr ⟨hu, hpair.1⟩)
    (Finset.mem_inter.mpr ⟨hv, hpair.2⟩) hx)).1

noncomputable def AvailableBadPairsAt (c : Int) (Ω : Finset Int)
    (F : Finset (Finset Int)) : Finset (Finset Int) := by
  classical
  exact Ω.powerset.filter (fun Q => Q.card = 2 ∧ c ∉ Q ∧
    ¬ IsAP (insert c Q) ∧ ∀ T ∈ F, IsAP T → ¬ Q ⊆ T)

theorem private_resource_at_root_exists
    {Ω : Finset Int} {F : Finset (Finset Int)} {c : Int}
    (hlegal : Legal Ω F) (hroot : Rooted F c)
    {S : Finset Int} (hSF : S ∈ F) (hS : ¬ IsAP S) :
    ∃ Q ∈ AvailableBadPairsAt c Ω F, Q ⊆ S ∧
      ∀ T ∈ F, T ≠ S → ¬ Q ⊆ T := by
  classical
  obtain ⟨u, hu, v, hv, huc, hvc, huv, hbad, hprivate⟩ :=
    private_pair_at_root_exists hlegal hroot hSF hS
  have hsub : ({u,v} : Finset Int) ⊆ S :=
    Finset.insert_subset_iff.mpr ⟨hu, Finset.singleton_subset_iff.mpr hv⟩
  have hp : ∀ T ∈ F, T ≠ S → ¬ ({u,v} : Finset Int) ⊆ T := by
    intro T hTF hTS hQT
    exact hprivate T hTF hTS ⟨hQT (by simp), hQT (by simp)⟩
  refine ⟨{u,v}, ?_, hsub, hp⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr (hsub.trans (hlegal.1 S hSF)), ?_⟩
  refine ⟨by simp [huv], by simp [Ne.symm huc, Ne.symm hvc], hbad, ?_⟩
  intro T hTF hT
  by_cases hTS : T = S
  · subst T
    exact (hS hT).elim
  · exact hp T hTF hTS

theorem crooked_members_card_le_available_pairs_at_root
    {Ω : Finset Int} {F : Finset (Finset Int)} {c : Int}
    (hlegal : Legal Ω F) (hroot : Rooted F c) :
    (CrookedMembers F).card ≤ (AvailableBadPairsAt c Ω F).card := by
  classical
  have hex : ∀ S : CrookedMembers F, ∃ Q : AvailableBadPairsAt c Ω F,
      Q.val ⊆ S.val ∧ ∀ T ∈ F, T ≠ S.val → ¬ Q.val ⊆ T := by
    intro S
    have hS := Finset.mem_filter.mp S.property
    obtain ⟨Q, hQ, hsub, hp⟩ := private_resource_at_root_exists hlegal hroot hS.1 hS.2
    exact ⟨⟨Q, hQ⟩, hsub, hp⟩
  choose f hf using hex
  apply Finset.card_le_card_of_injective (f := f)
  intro S T hST
  apply Subtype.ext
  by_contra hne
  have hTF := (Finset.mem_filter.mp T.property).1
  have hnot := (hf S).2 T.val hTF (Ne.symm hne)
  apply hnot
  rw [show (f S).val = (f T).val from congrArg Subtype.val hST]
  exact (hf T).1

#print axioms completion_least
#print axioms minimum_abs_gcd
#print axioms closed_isAP
#print axioms missing_completion_exists
#print axioms private_pair_exists
#print axioms private_resource_exists
#print axioms crooked_members_card_le_available_pairs
#print axioms mem_shift_iff
#print axioms isAP_shift_iff
#print axioms completionAt_least
#print axioms missing_completion_at_root_exists
#print axioms private_pair_at_root_exists
#print axioms private_resource_at_root_exists
#print axioms crooked_members_card_le_available_pairs_at_root

end JSP233.PrivatePairExistence
