module

public import Erdos272.Resources.N109474.CorrelatedSource109474

@[expose] public section

namespace JSP233.CorrelatedSource86412
open StarCompletion SourceBridge208 IntrinsicTriples208
open UnitFloorData158375 UnitFloor158375 StarArithmetic130000
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev Plan := CorrelatedSource118533.Plan

def Conditions (q : Plan) : Prop :=
  q.defect ≤ q.cutoff ∧ q.cutoff ≤ q.lower ∧ 12 ≤ q.lower-q.cutoff+1 ∧
  ∀ i ∈ Finset.range (q.cutoff-q.defect),
    q.target ≤ (q.defect+i) *
      (unitFloor (q.lower-(q.defect+i)) +
        Bonus CorrelatedSource118533.Primes (q.lower-(q.defect+i)))

instance (q : Plan) : Decidable (Conditions q) := by
  unfold Conditions
  infer_instance

theorem actual_plan_source_of_high {N : ℕ} {S : Finset ℤ} (q : Plan)
    (hq : Conditions q)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : q.lower ≤ S.card) (hdefect : q.defect ≤ Defect S)
    (hhigh : q.cutoff ≤ Defect S → q.target ≤ (Pool S).card) :
    q.target ≤ (Pool S).card := by
  have hcard : S.card ≤ N := by
    simpa only [ground_card] using Finset.card_le_card hground
  have hcutoff : q.cutoff ≤ q.lower := hq.2.1
  by_cases hc : q.cutoff ≤ Defect S
  · exact hhigh hc
  · have hmax := maxAPSize_le_card S
    have he : Defect S + MaxAPSize S = S.card := by unfold Defect; omega
    have ha₀ : q.lower-q.cutoff+1 ≤ MaxAPSize S := by omega
    have ha : 12 ≤ MaxAPSize S := hq.2.2.1.trans ha₀
    have hstar := CorrelatedSource118533.actual_eight_star_source hN hground hS ha
    have hl : q.lower-Defect S ≤ MaxAPSize S := by omega
    have hu := uniform_unit_floor hl (hmax.trans (hcard.trans hN))
    have hb := bonus_mono (Q := CorrelatedSource118533.Primes) hl
    have hprice := Nat.mul_le_mul_left (Defect S) (Nat.add_le_add hu hb)
    have hi : Defect S-q.defect ∈ Finset.range (q.cutoff-q.defect) :=
      Finset.mem_range.mpr (by omega)
    have hcert := hq.2.2.2 (Defect S-q.defect) hi
    have he' : q.defect+(Defect S-q.defect) = Defect S := by omega
    rw [he'] at hcert
    exact hcert.trans (hprice.trans hstar)

#print axioms actual_plan_source_of_high
end
end JSP233.CorrelatedSource86412
