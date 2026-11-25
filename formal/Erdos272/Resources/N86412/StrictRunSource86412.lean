module

public import Erdos272.Counting.N86412.StrictRunCount86412
public import Erdos272.Resources.N86412.StrictRunSourcePlan86412
public import Erdos272.Foundation.JSP233

@[expose] public section

namespace JSP233.StrictRunSource86412
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208 SourceFloorSound291012
open FastSource208 StrictRunCount86412
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem point_eq_price {s e h : ℕ} (hs : s ≤ 32753) : point s e h = Price s e h := by
  unfold point Price
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hqs : q ≤ 32753 := by have hh := (Finset.mem_Ico.mp hq).2; omega
  rw [FastDecode208.phi_correct q hqs]
  simp only [J, I, StrictRunCount86412.CountBound, StrictRunCount86412.multiplicity,
    fastMultiplicity_eq]

theorem actual_point_source {S : Finset ℤ} {e h : ℕ}
    (hS : 2 ≤ S.card) (hcap : S.card ≤ 32753) (he₂ : 2 ≤ e)
    (he : e ≤ Defect S) (hh : 1 ≤ h) (hha : h < S.card-e) :
    point S.card e h ≤ (Pool S).card := by
  rw [point_eq_price hcap]
  exact actual_run_source hS he₂ he hh hha

theorem actual_run_plan_source {N : ℕ} {S : Finset ℤ} (q : Plan)
    (hq : Conditions q) (hf : Floor q.upper q.defect q.target)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : q.lower ≤ S.card) (hdefect : q.defect ≤ Defect S) :
    q.target ≤ (Pool S).card := by
  have hcard : S.card ≤ N := by simpa only [ground_card] using Finset.card_le_card hground
  rcases hq with ⟨he₂, he, hl, hu, hlen, hpoints⟩
  by_cases hupper : q.upper ≤ S.card
  · exact (hf S.card hupper (by omega)).trans (actual_source_of_defect hS hdefect)
  · have hi : S.card-q.lower ∈ Finset.range q.heads.length :=
      Finset.mem_range.mpr (by omega)
    have hs : q.lower+(S.card-q.lower) = S.card := by omega
    have hc := hpoints (S.card-q.lower) hi
    rw [hs] at hc
    rcases hc with hshort | ⟨hh, hha, hp⟩
    · have hmax := maxAPSize_le_card S
      have htwo := two_le_maxAPSize hS
      unfold Defect at hdefect
      omega
    · exact hp.trans (actual_point_source hS (by omega) he₂ hdefect hh hha)

#print axioms point_eq_price
#print axioms actual_point_source
#print axioms actual_run_plan_source
end
end JSP233.StrictRunSource86412
