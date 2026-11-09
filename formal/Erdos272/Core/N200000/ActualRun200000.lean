module

public import Erdos272.Resources.SourceBridge208
public import Erdos272.Foundation.PrivateUnion
public import Erdos272.Arithmetic.APInterval208
public import Erdos272.Foundation.APGeometry
public import Erdos272.Core.NearAP36
public import Erdos272.Core.FarSlot112

@[expose] public section

/-! The unique full run in an actual source through a fixed point and
at a fixed positive step is constructed inside that source's powerset. -/
namespace JSP233.ActualRun200000
open StarCompletion APGeometry SourceBridge208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def RunFamily (S : Finset ℤ) (d x : ℤ) : Finset (Finset ℤ) :=
  S.powerset.filter (fun R => APAt d x R ∧ x ∈ R)

def Run (S : Finset ℤ) (d x : ℤ) : Finset ℤ := (RunFamily S d x).biUnion id

theorem singleton_at {d x : ℤ} (hd : 0 < d) : APAt d x {x} := by
  refine ⟨hd, x, x, ?_⟩
  intro y
  simp only [Finset.mem_singleton]
  constructor
  · intro he
    subst y
    exact ⟨le_rfl, le_rfl, by simp⟩
  · intro hy
    omega

theorem family_union_at {H : Finset (Finset ℤ)} {d x : ℤ} (hne : H.Nonempty)
    (hAt : ∀ R ∈ H, APAt d x R) (hroot : ∀ R ∈ H, x ∈ R) : APAt d x (H.biUnion id) := by
  induction H using Finset.induction_on with
  | empty => simp at hne
  | @insert R H hnot ih =>
      have hRAt := hAt R (Finset.mem_insert_self _ _)
      by_cases hH : H.Nonempty
      · have hHAt := ih hH (fun T hT => hAt T (Finset.mem_insert_of_mem hT))
          (fun T hT => hroot T (Finset.mem_insert_of_mem hT))
        obtain ⟨T, hT⟩ := hH
        have hxH : x ∈ H.biUnion id :=
          Finset.mem_biUnion.mpr ⟨T, hT, hroot T (Finset.mem_insert_of_mem hT)⟩
        rw [Finset.biUnion_insert]
        simpa only [APAt, Finset.mem_union, id_eq] using PrivateUnion.union_APAt d x
          (fun y => y ∈ R) (fun y => y ∈ H.biUnion id) hRAt hHAt
          (hroot R (Finset.mem_insert_self _ _)) hxH
      · have hHzero : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
        simpa only [hHzero, Finset.biUnion_insert, Finset.biUnion_empty, Finset.union_empty, id_eq] using hRAt

theorem run_family_nonempty {S : Finset ℤ} {d x : ℤ} (hd : 0 < d) (hx : x ∈ S) :
    (RunFamily S d x).Nonempty := by
  refine ⟨{x}, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hx),
    singleton_at hd, Finset.mem_singleton_self x⟩⟩

theorem run_subset (S : Finset ℤ) (d x : ℤ) : Run S d x ⊆ S := by
  intro y hy
  obtain ⟨R, hR, hyR⟩ := Finset.mem_biUnion.mp hy
  exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hR).1) hyR

theorem run_mem {S : Finset ℤ} {d x : ℤ} (hd : 0 < d) (hx : x ∈ S) : x ∈ Run S d x := by
  obtain ⟨R, hR⟩ := run_family_nonempty hd hx
  exact Finset.mem_biUnion.mpr ⟨R, hR, (Finset.mem_filter.mp hR).2.2⟩

theorem run_at {S : Finset ℤ} {d x : ℤ} (hd : 0 < d) (hx : x ∈ S) : APAt d x (Run S d x) :=
  family_union_at (run_family_nonempty hd hx)
    (fun _ hR => (Finset.mem_filter.mp hR).2.1) (fun _ hR => (Finset.mem_filter.mp hR).2.2)

theorem run_card {S : Finset ℤ} {d x : ℤ} (hd : 0 < d) (hx : x ∈ S) : (Run S d x).card ≤ MaxAPSize S :=
  AP_card_le_max ((isAP_iff_exists_APAt _).mpr ⟨d, x, run_at hd hx, run_mem hd hx⟩) (run_subset S d x)

theorem covers_subset_run {S R : Finset ℤ} {d x : ℤ}
    (hR : R ⊆ S) (hAt : APAt d x R) (hx : x ∈ R) : R ⊆ Run S d x := by
  intro y hy
  exact Finset.mem_biUnion.mpr ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hR, hAt, hx⟩, hy⟩

theorem intersection_coarser_at {P R : Finset ℤ} {d p g x : ℤ}
    (hP : APAt d p P) (hR : APAt g x R) (hgd : g ∣ d) (hgp : g ∣ p - x) : APAt d p (P ∩ R) := by
  obtain ⟨hd, lp, up, hpr⟩ := hP
  obtain ⟨_hg, lr, ur, hrr⟩ := hR
  refine ⟨hd, max lp lr, min up ur, ?_⟩
  intro y
  simp only [Finset.mem_inter, hpr, hrr, max_le_iff, le_min_iff]
  constructor
  · intro hy
    exact ⟨⟨hy.1.1, hy.2.1⟩, ⟨hy.1.2.1, hy.2.2.1⟩, hy.1.2.2⟩
  · intro hy
    have hgy : g ∣ y - x := by
      rw [show y - x = (y - p) + (p - x) by ring]
      exact dvd_add (dvd_trans hgd hy.2.2) hgp
    exact ⟨⟨hy.1.1, hy.2.1.1, hy.2.2⟩, hy.1.2, hy.2.1.2, hgy⟩

#print axioms singleton_at
#print axioms family_union_at
#print axioms run_family_nonempty
#print axioms run_subset
#print axioms run_mem
#print axioms run_at
#print axioms run_card
#print axioms covers_subset_run
#print axioms intersection_coarser_at
end
end JSP233.ActualRun200000
