module

public import Erdos272.Foundation.StarCompletion
public import Erdos272.Foundation.StaircaseCertificate
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.GCD
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
Unbounded geometric downclosure for actual unit-step intervals through zero.
The rectangular closure retains virtual cells of length below four; demand
is filtered separately. Actual primitive bad-pair pools are unchanged.
This module does not assert the concrete ColumnScore supply formula or any
finite certificate, analytic tail, or full StarBound theorem.
-/

namespace JSP233.StaircaseGeometry

open StarCompletion
open scoped BigOperators

def Window (l r : Nat) : Finset Int := Finset.Icc (-(l : Int)) (r : Int)

theorem mem_window (l r : Nat) (x : Int) :
    x ∈ Window l r ↔ -(l : Int) ≤ x ∧ x ≤ (r : Int) := by
  simp [Window]

theorem zero_mem_window (l r : Nat) : 0 ∈ Window l r := by
  simp [Window]

theorem window_isAP (l r : Nat) : IsAP (Window l r) := by
  refine ⟨1, 0, by decide, -(l : Int), r, ?_, zero_mem_window l r⟩
  intro x
  simp [Window]

theorem window_card (l r : Nat) : (Window l r).card = l+r+1 := by
  simp only [Window, Int.card_Icc]
  omega

theorem window_mono {l r L R : Nat} (hl : l ≤ L) (hr : r ≤ R) :
    Window l r ⊆ Window L R := by
  intro x hx
  rw [mem_window] at hx ⊢
  constructor <;> omega

theorem window_injective : Function.Injective (fun p : Nat × Nat => Window p.1 p.2) := by
  intro p q heq
  change Window p.1 p.2 = Window q.1 q.2 at heq
  have hpL : -(p.1 : Int) ∈ Window q.1 q.2 := by
    rw [← heq]
    simp [Window]
  have hqL : -(q.1 : Int) ∈ Window p.1 p.2 := by
    rw [heq]
    simp [Window]
  have hpR : (p.2 : Int) ∈ Window q.1 q.2 := by
    rw [← heq]
    simp [Window]
  have hqR : (q.2 : Int) ∈ Window p.1 p.2 := by
    rw [heq]
    simp [Window]
  rw [mem_window] at hpL hqL hpR hqR
  apply Prod.ext <;> omega

/-- Actual unordered, noncentral, primitive bad pairs. -/
def IsPrimitiveBadPair (Q : Finset Int) : Prop :=
  Q.card = 2 ∧ 0 ∉ Q ∧ ¬ IsAP (insert 0 Q) ∧
    ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → Int.gcd u v = 1

noncomputable def PrimitiveBadPairs (S : Finset Int) : Finset (Finset Int) := by
  classical
  exact S.powerset.filter IsPrimitiveBadPair

theorem mem_primitiveBadPairs (S Q : Finset Int) :
    Q ∈ PrimitiveBadPairs S ↔ Q ⊆ S ∧ IsPrimitiveBadPair Q := by
  classical
  simp [PrimitiveBadPairs]

theorem primitiveBadPairs_mono {S T : Finset Int} (hST : S ⊆ T) :
    PrimitiveBadPairs S ⊆ PrimitiveBadPairs T := by
  intro Q hQ
  rw [mem_primitiveBadPairs] at hQ ⊢
  exact ⟨hQ.1.trans hST, hQ.2⟩

noncomputable def PrimitivePool (F : Finset (Finset Int)) : Finset (Finset Int) :=
  F.biUnion PrimitiveBadPairs

theorem primitivePool_mono {F G : Finset (Finset Int)} (hFG : F ⊆ G) :
    PrimitivePool F ⊆ PrimitivePool G := by
  classical
  intro Q hQ
  obtain ⟨S, hS, hQ⟩ := Finset.mem_biUnion.mp hQ
  exact Finset.mem_biUnion.mpr ⟨S, hFG hS, hQ⟩

def Family (C : Finset (Nat × Nat)) : Finset (Finset Int) :=
  C.image (fun p => Window p.1 p.2)

theorem family_card (C : Finset (Nat × Nat)) : (Family C).card = C.card := by
  exact Finset.card_image_of_injective C window_injective

theorem family_mono {C D : Finset (Nat × Nat)} (hCD : C ⊆ D) : Family C ⊆ Family D :=
  Finset.image_subset_image hCD

def Box (p : Nat × Nat) : Finset (Nat × Nat) :=
  (Finset.range (p.1+1)).product (Finset.range (p.2+1))

/-- Retains virtual small cells; the large-member condition is separate. -/
def Down (C : Finset (Nat × Nat)) : Finset (Nat × Nat) := C.biUnion Box

theorem mem_down (C : Finset (Nat × Nat)) (q : Nat × Nat) :
    q ∈ Down C ↔ ∃ p ∈ C, q.1 ≤ p.1 ∧ q.2 ≤ p.2 := by
  simp [Down, Box, Nat.lt_succ_iff]

theorem subset_down (C : Finset (Nat × Nat)) : C ⊆ Down C := by
  intro p hp
  exact (mem_down C p).mpr ⟨p, hp, le_rfl, le_rfl⟩

theorem down_closed {C : Finset (Nat × Nat)} {p q : Nat × Nat}
    (hp : p ∈ Down C) (hl : q.1 ≤ p.1) (hr : q.2 ≤ p.2) : q ∈ Down C := by
  obtain ⟨t, ht, hlt, hrt⟩ := (mem_down C p).mp hp
  exact (mem_down C q).mpr ⟨t, ht, hl.trans hlt, hr.trans hrt⟩

theorem down_idempotent (C : Finset (Nat × Nat)) : Down (Down C) = Down C := by
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨q, hq, hl, hr⟩ := (mem_down (Down C) p).mp hp
    exact down_closed hq hl hr
  · exact subset_down (Down C)

/-- Every new actual interval is contained in an original actual interval. -/
theorem down_member_subset_original {C : Finset (Nat × Nat)} {S : Finset Int}
    (hS : S ∈ Family (Down C)) : ∃ T ∈ Family C, S ⊆ T := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨p, hp, hl, hr⟩ := (mem_down C q).mp hq
  exact ⟨Window p.1 p.2, Finset.mem_image.mpr ⟨p, hp, rfl⟩, window_mono hl hr⟩

theorem down_primitivePool_eq (C : Finset (Nat × Nat)) :
    PrimitivePool (Family (Down C)) = PrimitivePool (Family C) := by
  classical
  apply Finset.Subset.antisymm
  · intro Q hQ
    obtain ⟨S, hS, hQS⟩ := Finset.mem_biUnion.mp hQ
    obtain ⟨T, hT, hST⟩ := down_member_subset_original hS
    exact Finset.mem_biUnion.mpr ⟨T, hT, primitiveBadPairs_mono hST hQS⟩
  · exact primitivePool_mono (family_mono (subset_down C))

def Valid (p : Nat × Nat) : Prop := 3 ≤ p.1 + p.2

instance : DecidablePred Valid := fun p => inferInstanceAs (Decidable (3 ≤ p.1+p.2))

theorem valid_iff_large_window (p : Nat × Nat) :
    Valid p ↔ 4 ≤ (Window p.1 p.2).card := by
  rw [window_card]
  unfold Valid
  omega

def ValidDown (C : Finset (Nat × Nat)) : Finset (Nat × Nat) :=
  (Down C).filter Valid

theorem subset_validDown {C : Finset (Nat × Nat)}
    (hvalid : ∀ p ∈ C, Valid p) : C ⊆ ValidDown C := by
  intro p hp
  exact Finset.mem_filter.mpr ⟨subset_down C hp, hvalid p hp⟩

theorem validDown_primitivePool_eq {C : Finset (Nat × Nat)}
    (hvalid : ∀ p ∈ C, Valid p) :
    PrimitivePool (Family (ValidDown C)) = PrimitivePool (Family C) := by
  apply Finset.Subset.antisymm
  · have h := primitivePool_mono (family_mono (Finset.filter_subset Valid (Down C)))
    rw [down_primitivePool_eq C] at h
    exact h
  · exact primitivePool_mono (family_mono (subset_validDown hvalid))

theorem validDown_demand_mono {C : Finset (Nat × Nat)}
    (hvalid : ∀ p ∈ C, Valid p) :
    (Family C).card ≤ (Family (ValidDown C)).card :=
  Finset.card_le_card (family_mono (subset_validDown hvalid))

def Width (C : Finset (Nat × Nat)) : Nat := C.sup Prod.snd

def Height (C : Finset (Nat × Nat)) : Nat := C.sup Prod.fst

def Column (C : Finset (Nat × Nat)) (r : Nat) : Finset (Nat × Nat) :=
  (Down C).filter (fun p => p.2 = r)

/-- Encoded height: 0 means absent, h+1 means actual height h. -/
def Profile (C : Finset (Nat × Nat)) (r : Nat) : Nat :=
  (Column C r).sup (fun p => p.1+1)

theorem mem_down_iff_profile (C : Finset (Nat × Nat)) (l r : Nat) :
    (l,r) ∈ Down C ↔ l < Profile C r := by
  constructor
  · intro hp
    have hcol : (l,r) ∈ Column C r := Finset.mem_filter.mpr ⟨hp, rfl⟩
    have hle : l+1 ≤ Profile C r :=
      Finset.le_sup (f := fun p : Nat × Nat => p.1+1) hcol
    omega
  · intro hp
    have hle : l+1 ≤ (Column C r).sup (fun p => p.1+1) := by
      change l+1 ≤ Profile C r
      omega
    obtain ⟨p, hp, hpl⟩ := (Finset.le_sup_iff (by omega : 0 < l+1)).mp hle
    have hp' := Finset.mem_filter.mp hp
    exact down_closed hp'.1 (by omega) (by omega)

theorem profile_antitone (C : Finset (Nat × Nat)) : Antitone (Profile C) := by
  intro r s hrs
  unfold Profile
  apply Finset.sup_le
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpr : (p.1,r) ∈ Down C := down_closed hp'.1 le_rfl (by omega)
  have hcol : (p.1,r) ∈ Column C r := Finset.mem_filter.mpr ⟨hpr, rfl⟩
  exact Finset.le_sup (b := (p.1,r)) (f := fun p : Nat × Nat => p.1+1) hcol

theorem profile_height_bound (C : Finset (Nat × Nat)) (r : Nat) :
    Profile C r ≤ Height C + 1 := by
  apply Finset.sup_le
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).1
  obtain ⟨q, hq, hl, hr⟩ := (mem_down C p).mp hp'
  have hqle : q.1 ≤ Height C := Finset.le_sup hq
  omega

theorem profile_zero_iff (C : Finset (Nat × Nat)) (r : Nat) :
    Profile C r = 0 ↔ ¬ ∃ l, (l,r) ∈ Down C := by
  constructor
  · intro hz ⟨l, hl⟩
    have hlt := (mem_down_iff_profile C l r).mp hl
    omega
  · intro hn
    by_contra hz
    apply hn
    exact ⟨0, (mem_down_iff_profile C 0 r).mpr (by omega)⟩

theorem down_width_bound {C : Finset (Nat × Nat)} {p : Nat × Nat}
    (hp : p ∈ Down C) : p.2 ≤ Width C := by
  obtain ⟨q, hq, hl, hr⟩ := (mem_down C p).mp hp
  exact hr.trans (Finset.le_sup hq)

theorem profile_zero_of_width_lt (C : Finset (Nat × Nat)) {r : Nat}
    (hr : Width C < r) : Profile C r = 0 := by
  apply (profile_zero_iff C r).mpr
  rintro ⟨l, hl⟩
  have hle := down_width_bound hl
  omega

def DemandSlice (p : Nat → Nat) (r : Nat) : Finset (Nat × Nat) :=
  ((Finset.range (p r)).filter (fun l => 3 ≤ l+r)).image (fun l => (l,r))

theorem mem_demandSlice (p : Nat → Nat) (r : Nat) (q : Nat × Nat) :
    q ∈ DemandSlice p r ↔ q.2 = r ∧ q.1 < p r ∧ Valid q := by
  constructor
  · intro hq
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
    have hl' := Finset.mem_filter.mp hl
    exact ⟨rfl, Finset.mem_range.mp hl'.1, hl'.2⟩
  · rintro ⟨hr, hl, hv⟩
    refine Finset.mem_image.mpr ⟨q.1, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_range.mpr hl
    · simpa [Valid, hr] using hv
    · exact Prod.ext rfl hr.symm

theorem demandSlice_disjoint (p : Nat → Nat) {r s : Nat} (hrs : r ≠ s) :
    Disjoint (DemandSlice p r) (DemandSlice p s) := by
  apply Finset.disjoint_left.mpr
  intro q hqr hqs
  have hqr' := (mem_demandSlice p r q).mp hqr
  have hqs' := (mem_demandSlice p s q).mp hqs
  exact hrs (hqr'.1.symm.trans hqs'.1)

theorem validDown_eq_slices (C : Finset (Nat × Nat)) :
    ValidDown C = (Finset.range (Width C+1)).biUnion (DemandSlice (Profile C)) := by
  ext q
  constructor
  · intro hq
    have hq' := Finset.mem_filter.mp hq
    apply Finset.mem_biUnion.mpr
    refine ⟨q.2, Finset.mem_range.mpr (by have := down_width_bound hq'.1; omega), ?_⟩
    exact (mem_demandSlice (Profile C) q.2 q).mpr
      ⟨rfl, (mem_down_iff_profile C q.1 q.2).mp hq'.1, hq'.2⟩
  · intro hq
    obtain ⟨r, hr, hqr⟩ := Finset.mem_biUnion.mp hq
    have hq' := (mem_demandSlice (Profile C) r q).mp hqr
    apply Finset.mem_filter.mpr
    refine ⟨(mem_down_iff_profile C q.1 q.2).mpr ?_, hq'.2.2⟩
    simpa [hq'.1] using hq'.2.1

theorem demandSlice_card (p : Nat → Nat) (r : Nat) :
    (DemandSlice p r).card = p r - (3-r) := by
  have hinj : Function.Injective (fun l : Nat => (l,r)) := by
    intro a b h
    exact congrArg Prod.fst h
  rw [DemandSlice, Finset.card_image_of_injective _ hinj]
  have heq : (Finset.range (p r)).filter (fun l => 3 ≤ l+r) =
      Finset.Ico (3-r) (p r) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [heq, Nat.card_Ico]

theorem validDown_card_sum (C : Finset (Nat × Nat)) :
    (ValidDown C).card =
      ∑ r ∈ Finset.range (Width C+1), (Profile C r - (3-r)) := by
  have hd : ((Finset.range (Width C+1) : Finset Nat) : Set Nat).PairwiseDisjoint
      (DemandSlice (Profile C)) := by
    intro r hr s hs hrs
    exact demandSlice_disjoint (Profile C) hrs
  rw [validDown_eq_slices, Finset.card_biUnion hd]
  exact Finset.sum_congr rfl (fun r hr => demandSlice_card (Profile C) r)

/-- The demand term only: no primitive supply is hidden in this score. -/
def DemandScore (r i : Nat) : Int := ((i - (3-r) : Nat) : Int)

theorem validDown_demand_profileScore (C : Finset (Nat × Nat)) :
    ((Family (ValidDown C)).card : Int) =
      StaircaseCertificate.ProfileScore DemandScore (Profile C) (Width C) := by
  rw [family_card, validDown_card_sum]
  simp [StaircaseCertificate.ProfileScore, DemandScore]

theorem original_demand_le_profileScore {C : Finset (Nat × Nat)}
    (hvalid : ∀ p ∈ C, Valid p) :
    ((Family C).card : Int) ≤
      StaircaseCertificate.ProfileScore DemandScore (Profile C) (Width C) := by
  rw [← validDown_demand_profileScore]
  exact_mod_cast validDown_demand_mono hvalid

/-- Normalize an actual finite family of large unit intervals, without
assuming a preselected coordinate encoding or any resource-count bound. -/
theorem exists_coordinates (F : Finset (Finset Int))
    (hF : ∀ S ∈ F, ∃ l r : Nat, S = Window l r ∧ 4 ≤ S.card) :
    ∃ C : Finset (Nat × Nat), Family C = F ∧ ∀ p ∈ C, Valid p := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty =>
    intro hF
    exact ⟨∅, by simp [Family], by simp⟩
  | @insert S F hnot ih =>
    intro hF
    obtain ⟨l, r, hS, hlarge⟩ := hF S (Finset.mem_insert_self _ _)
    obtain ⟨C, hC, hvalid⟩ := ih (by
      intro T hT
      exact hF T (Finset.mem_insert_of_mem hT))
    refine ⟨insert (l,r) C, ?_, ?_⟩
    · change (insert (l,r) C).image (fun p => Window p.1 p.2) = insert S F
      rw [Finset.image_insert]
      change insert (Window l r) (Family C) = insert S F
      rw [hC, ← hS]
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · apply (valid_iff_large_window (l,r)).mpr
        simpa [← hS] using hlarge
      · exact hvalid p hp

theorem actual_family_downclosure (F : Finset (Finset Int))
    (hF : ∀ S ∈ F, ∃ l r : Nat, S = Window l r ∧ 4 ≤ S.card) :
    ∃ C : Finset (Nat × Nat), Family C = F ∧
      F ⊆ Family (ValidDown C) ∧
      PrimitivePool (Family (ValidDown C)) = PrimitivePool F ∧
      (F.card : Int) ≤ StaircaseCertificate.ProfileScore DemandScore (Profile C) (Width C) ∧
      Antitone (Profile C) := by
  obtain ⟨C, hC, hvalid⟩ := exists_coordinates F hF
  refine ⟨C, hC, ?_, ?_, ?_, profile_antitone C⟩
  · rw [← hC]
    exact family_mono (subset_validDown hvalid)
  · rw [← hC]
    exact validDown_primitivePool_eq hvalid
  · rw [← hC]
    exact original_demand_le_profileScore hvalid

#print axioms mem_window
#print axioms zero_mem_window
#print axioms window_isAP
#print axioms window_card
#print axioms window_mono
#print axioms window_injective
#print axioms mem_primitiveBadPairs
#print axioms primitiveBadPairs_mono
#print axioms primitivePool_mono
#print axioms family_card
#print axioms family_mono
#print axioms mem_down
#print axioms subset_down
#print axioms down_closed
#print axioms down_idempotent
#print axioms down_member_subset_original
#print axioms down_primitivePool_eq
#print axioms valid_iff_large_window
#print axioms subset_validDown
#print axioms validDown_primitivePool_eq
#print axioms validDown_demand_mono
#print axioms mem_down_iff_profile
#print axioms profile_antitone
#print axioms profile_height_bound
#print axioms profile_zero_iff
#print axioms down_width_bound
#print axioms profile_zero_of_width_lt
#print axioms mem_demandSlice
#print axioms demandSlice_disjoint
#print axioms validDown_eq_slices
#print axioms demandSlice_card
#print axioms validDown_card_sum
#print axioms validDown_demand_profileScore
#print axioms original_demand_le_profileScore
#print axioms exists_coordinates
#print axioms actual_family_downclosure

end JSP233.StaircaseGeometry
