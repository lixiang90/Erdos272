module

public import Erdos272.Core.N200000.RunTrace200000

@[expose] public section

/-! A coverable core pair and outside point force both pair points
into the same actual primitive run. No new source-mass oracle is used. -/
namespace JSP233.CorePairHull200000
open StarCompletion APGeometry SourceBridge208 NearAP36 FarSlot112 IntrinsicTriples208
open ActualRun200000 RunTrace200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem actual_cover_pair_in_run {S : Finset ℤ} {a b x g : ℤ} (hab : a < b)
    (hgeq : (Int.gcd (b - a) (x - a) : ℤ) = g)
    (hcover : ∃ R : Finset ℤ, IsAP R ∧ ({x, a, b} : Finset ℤ) ⊆ R ∧ R ⊆ S) :
    a ∈ Run S g x ∧ b ∈ Run S g x := by
  obtain ⟨R, hR, hpoints, hRS⟩ := hcover
  have haR : a ∈ R := hpoints (by simp)
  have hbR : b ∈ R := hpoints (by simp)
  have hxR : x ∈ R := hpoints (by simp)
  have hg : 0 < g := by
    rw [← hgeq]
    exact_mod_cast Int.gcd_pos_of_ne_zero_left (x - a) (by omega : b - a ≠ 0)
  have hga : g ∣ x - a := by rw [← hgeq]; exact Int.gcd_dvd_right _ _
  have hgb : g ∣ b - a := by rw [← hgeq]; exact Int.gcd_dvd_left _ _
  let T := FarSlot112.Segment g a (min a x) (max b x)
  have hTS : T ⊆ S := by
    have habEq : a + (b - a) = b := by omega
    have hh := primitive_segment_subset (d := b - a) (a := a) (l := a) (r := b) (x := x) hR
      haR (by simpa only [habEq] using hbR) haR hbR hxR
    rw [hgeq] at hh
    exact hh.trans hRS
  have hxT : x ∈ T := mem_segment.mpr ⟨min_le_right _ _, le_max_right _ _, hga⟩
  have haT : a ∈ T := mem_segment.mpr ⟨min_le_left _ _, hab.le.trans (le_max_left _ _), by simp⟩
  have hbT : b ∈ T := mem_segment.mpr ⟨(min_le_left _ _).trans hab.le, le_max_left _ _, hgb⟩
  have hTR := covers_subset_run hTS (apAt_rebase (segment_APAt hg) hxT) hxT
  exact ⟨hTR haT, hTR hbT⟩

theorem same_step_run_disjoint_core {S P : Finset ℤ} {d p x : ℤ}
    (hP : MaximalAPCore S P) (hAt : APAt d p P) (hx : x ∈ S \ P) : Disjoint P (Run S d x) := by
  apply Finset.disjoint_left.mpr
  intro y hyP hyR
  have hxS := (Finset.mem_sdiff.mp hx).1
  have hxP := (Finset.mem_sdiff.mp hx).2
  have hRAt := run_at hAt.1 hxS
  have hUAt : APAt d y (P ∪ Run S d x) := by
    simpa only [APAt, Finset.mem_union] using PrivateUnion.union_APAt d y
      (fun z => z ∈ P) (fun z => z ∈ Run S d x)
      (apAt_rebase hAt hyP) (apAt_rebase hRAt hyR) hyP hyR
  have hUAP : IsAP (P ∪ Run S d x) :=
    (isAP_iff_exists_APAt _).mpr ⟨d, y, hUAt, Finset.mem_union_left _ hyP⟩
  have hEq := hP.2.2 (P ∪ Run S d x) Finset.subset_union_left
    (Finset.union_subset hP.1 (run_subset S d x)) hUAP
  exact hxP (hEq ▸ Finset.mem_union_right P (run_mem hAt.1 hxS))

theorem outside_run_pool {S : Finset ℤ} {a b x g : ℤ}
    (hx : x ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hxa : x ≠ a) (hxb : x ≠ b) (hab : a < b)
    (hgeq : (Int.gcd (b - a) (x - a) : ℤ) = g)
    (hmiss : a ∉ Run S g x ∨ b ∉ Run S g x) : ({x, a, b} : Finset ℤ) ∈ Pool S := by
  apply mem_pool.mpr
  refine ⟨Finset.insert_subset_iff.mpr ⟨hx, Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩⟩,
    by simp [hxa, hxb, hab.ne], ?_⟩
  intro hcover
  have hh := actual_cover_pair_in_run hab hgeq hcover
  rcases hmiss with hm | hm
  · exact hm hh.1
  · exact hm hh.2

theorem same_phase_pool {S P : Finset ℤ} {d p a b x : ℤ}
    (hP : MaximalAPCore S P) (hAt : APAt d p P) (hx : x ∈ S \ P)
    (ha : a ∈ P) (hb : b ∈ P) (hab : a < b)
    (hgeq : (Int.gcd (b - a) (x - a) : ℤ) = d) : ({x, a, b} : Finset ℤ) ∈ Pool S := by
  have hxS := (Finset.mem_sdiff.mp hx).1
  have hxP := (Finset.mem_sdiff.mp hx).2
  have hxa : x ≠ a := by intro he; exact hxP (he ▸ ha)
  have hxb : x ≠ b := by intro he; exact hxP (he ▸ hb)
  have hdis := same_step_run_disjoint_core hP hAt hx
  exact outside_run_pool hxS (hP.1 ha) (hP.1 hb) hxa hxb hab hgeq
    (Or.inl (fun hh => Finset.disjoint_left.mp hdis ha hh))

theorem outside_padded_trace_pool {S : Finset ℤ} {p d g x : ℤ} {a i j : ℕ} {J : Finset ℕ}
    (hd : 0 < d) (hi : i < a) (hj : j < a) (hij : i < j) (hx : x ∈ S)
    (hpoints : ∀ k < a, p + d * (k : ℤ) ∈ S) (hxnot : ∀ k < a, x ≠ p + d * (k : ℤ))
    (htrace : Trace a p d (Run S g x) ⊆ J) (hmiss : ¬ (i ∈ J ∧ j ∈ J))
    (hgeq : (Int.gcd ((p + d * (j : ℤ)) - (p + d * (i : ℤ))) (x - (p + d * (i : ℤ))) : ℤ) = g) :
    ({x, p + d * (i : ℤ), p + d * (j : ℤ)} : Finset ℤ) ∈ Pool S := by
  have hab : p + d * (i : ℤ) < p + d * (j : ℤ) := by
    have hZ : (i : ℤ) < j := by exact_mod_cast hij
    nlinarith only [hd, hZ]
  apply outside_run_pool hx (hpoints i hi) (hpoints j hj) (hxnot i hi) (hxnot j hj) hab hgeq
  by_cases hRi : p + d * (i : ℤ) ∈ Run S g x
  · exact Or.inr (fun hRj => hmiss ⟨htrace (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hRi⟩),
      htrace (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hRj⟩)⟩)
  · exact Or.inl hRi

#print axioms actual_cover_pair_in_run
#print axioms same_step_run_disjoint_core
#print axioms outside_run_pool
#print axioms same_phase_pool
#print axioms outside_padded_trace_pool
end
end JSP233.CorePairHull200000
