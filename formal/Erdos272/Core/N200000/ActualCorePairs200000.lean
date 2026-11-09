module

public import Erdos272.Core.N200000.IndexedCorePairs200000

@[expose] public section

/-! Select an actual longest AP, the actual primitive normalization, and
one padded run interval. A pure index-pair lower certificate pays e times
its value into the same intrinsic pool. -/
namespace JSP233.ActualCorePairs200000
open StarCompletion APGeometry SourceBridge208 NearAP36 IntrinsicTriples208
open ActualRun200000 RunTrace200000 PairPool200000 CoreNormal200000 IndexedCorePairs200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem actual_source_core {S : Finset ℤ} (hS : 2 ≤ S.card) :
    ∃ (P : Finset ℤ) (d p : ℤ), 0 < d ∧ P ⊆ S ∧ P.card = MaxAPSize S ∧
      MaximalAPCore S P ∧ APAt d p P ∧
        P = (Finset.range (MaxAPSize S)).image (fun i : ℕ => p + d * (i : ℤ)) := by
  let A := S.powerset.filter IsAP
  have hA : A.Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    refine ⟨{x, y}, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, pair_isAP x y⟩⟩
    exact Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image A Finset.card hA
  have hPS : P ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
  have hAP : IsAP P := (Finset.mem_filter.mp hP).2
  have hcard : P.card = MaxAPSize S := by
    apply Nat.le_antisymm (AP_card_le_max hAP hPS)
    exact Finset.sup_le hmax
  have hPmax : MaximalAPCore S P := by
    refine ⟨hPS, hAP, ?_⟩
    intro U hPU hUS hU
    have hbound : U.card ≤ P.card := by rw [hcard]; exact AP_card_le_max hU hUS
    exact (Finset.eq_of_subset_of_card_le hPU hbound).symm
  obtain ⟨d, p, hAt, hp⟩ := (isAP_iff_exists_APAt _).mp hAP
  have hne : P.Nonempty := ⟨p, hp⟩
  refine ⟨P, d, P.min' hne, hAt.1, hPS, hcard, hPmax,
    apAt_rebase hAt (Finset.min'_mem _ hne), ?_⟩
  simpa only [hcard] using apAt_eq_range hAt hne

theorem actual_point_index_certificate {S P : Finset ℤ} {p d x : ℤ} {a : ℕ}
    (hd : 0 < d) (hP : MaximalAPCore S P) (hAt : APAt d p P)
    (hgrid : P = (Finset.range a).image (fun i : ℕ => p + d * (i : ℤ)))
    (hmax : MaxAPSize S ≤ a) (hx : x ∈ S \ P) :
    ∃ n : Normalization d (x - p), ∃ l : ℕ, l + ExceptionLength a n.h ≤ a ∧
      (GoodIndex a n.h n.ell (Finset.Ico l (l + ExceptionLength a n.h))).card ≤ (GoodPairs S P x).card := by
  obtain ⟨n⟩ := actual_normalization hd (x - p)
  by_cases hone : n.h = 1
  · refine ⟨n, 0, by simp [ExceptionLength, hone], ?_⟩
    exact actual_index_pair_count hd hP hAt hgrid hx n (Or.inl hone)
  · have hxS := (Finset.mem_sdiff.mp hx).1
    have hgd : n.g ∣ d := ⟨(n.h : ℤ), by nlinarith only [n.step_eq]⟩
    have hyg : n.g ∣ x - p := ⟨n.ell, by nlinarith only [n.point_eq]⟩
    have hgp : n.g ∣ p - x := by
      rw [show p - x = -(x - p) by ring]
      exact dvd_neg.mpr hyg
    have hTrace : Trace a p d (Run S n.g x) ⊆ Finset.range a := Finset.filter_subset _ _
    have hbetween : ∀ i ∈ Trace a p d (Run S n.g x), ∀ k ∈ Trace a p d (Run S n.g x),
        ∀ j, i ≤ j → j ≤ k → j ∈ Trace a p d (Run S n.g x) := by
      intro i hi k hk j hij hjk
      exact trace_between hd (run_at n.g_pos hxS) hgd hi hk hij hjk
    have hcardA : (Trace a p d (Run S n.g x)).card ≤ a := by
      simpa only [Finset.card_range] using Finset.card_le_card hTrace
    have hcardH : (Trace a p d (Run S n.g x)).card ≤ (a + n.h - 1) / n.h := by
      rw [trace_card_eq a hd (Run S n.g x), ← hgrid]
      exact actual_run_core_card hAt n.g_pos hxS hmax n.h_pos n.step_eq hgp
    have hcard : (Trace a p d (Run S n.g x)).card ≤ ExceptionLength a n.h := by
      simp only [ExceptionLength, if_neg hone]
      exact le_min hcardA hcardH
    have hb : ExceptionLength a n.h ≤ a := by
      simp only [ExceptionLength, if_neg hone]
      exact min_le_left _ _
    obtain ⟨l, hlen, hsub⟩ := pad_same_interval hTrace hbetween hcard hb
    exact ⟨n, l, hlen, actual_index_pair_count hd hP hAt hgrid hx n (Or.inr hsub)⟩

theorem actual_defect_source_of_index_bound {S : Finset ℤ} {U : ℕ} (hS : 2 ≤ S.card)
    (hc : ∀ h : ℕ, 0 < h → ∀ ell : ℤ, Int.gcd (h : ℤ) ell = 1 → ∀ l : ℕ,
      l + ExceptionLength (MaxAPSize S) h ≤ MaxAPSize S →
        U ≤ (GoodIndex (MaxAPSize S) h ell (Finset.Ico l (l + ExceptionLength (MaxAPSize S) h))).card) :
    Defect S * U ≤ (Pool S).card := by
  obtain ⟨P, d, p, hd, hPS, hcard, hP, hAt, hgrid⟩ := actual_source_core hS
  apply actual_defect_pair_source hPS hcard
  intro x hx
  obtain ⟨n, l, hlen, hpairs⟩ := actual_point_index_certificate hd hP hAt hgrid le_rfl hx
  exact (hc n.h n.h_pos n.ell n.coprime l hlen).trans hpairs

#print axioms actual_source_core
#print axioms actual_point_index_certificate
#print axioms actual_defect_source_of_index_bound
end
end JSP233.ActualCorePairs200000
