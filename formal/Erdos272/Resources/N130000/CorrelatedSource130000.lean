module

public import Erdos272.Core.N130000.StarCore130000
public import Erdos272.Resources.N158375.CorrelatedSource158375

@[expose] public section

namespace JSP233.CorrelatedSource130000
open StarCompletion SourceBridge208 IntrinsicTriples208 SourceFloorSound291012
open CoreUnionSource200000 UnitFloorData158375 UnitFloor158375 StarCore130000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev Plan := CorrelatedSource158375.Plan

def Conditions (q : Plan) : Prop :=
  q.defect ≤ q.cutoff ∧ q.cutoff ≤ q.lower ∧ 12 ≤ q.lower-q.cutoff+1 ∧
  ∀ i ∈ Finset.range (q.cutoff-q.defect),
    q.target ≤ (q.defect+i) *
      (unitFloor (q.lower-(q.defect+i))+
        ((q.lower-q.cutoff+1)/6).choose 2+((q.lower-q.cutoff+1)/10).choose 2)

instance (q : Plan) : Decidable (Conditions q) := by unfold Conditions; infer_instance

theorem actual_plan_source {N : ℕ} {S : Finset ℤ} (q : Plan)
    (hq : Conditions q) (hf : Floor q.lower q.cutoff q.target)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : q.lower ≤ S.card) (hdefect : q.defect ≤ Defect S) :
    q.target ≤ (Pool S).card := by
  have hcard : S.card ≤ N := by simpa only [ground_card] using Finset.card_le_card hground
  have hcutoff : q.cutoff ≤ q.lower := hq.2.1
  by_cases hhigh : q.cutoff ≤ Defect S
  · exact (hf S.card hsize (by norm_num at *; omega)).trans (actual_source_of_defect hS hhigh)
  · have hmax := maxAPSize_le_card S
    have he : Defect S+MaxAPSize S = S.card := by unfold Defect; omega
    have ha₀ : q.lower-q.cutoff+1 ≤ MaxAPSize S := by omega
    have ha : 12 ≤ MaxAPSize S := hq.2.2.1.trans ha₀
    have hstar := actual_two_star_source hN hground hS ha
    have hu := uniform_unit_floor (show q.lower-Defect S ≤ MaxAPSize S by omega)
      (hmax.trans (hcard.trans hN))
    have hb : ((q.lower-q.cutoff+1)/6).choose 2+((q.lower-q.cutoff+1)/10).choose 2 ≤
        (MaxAPSize S/6).choose 2+(MaxAPSize S/10).choose 2 := by
      simpa [StarArithmetic130000.Bonus] using
        (StarArithmetic130000.bonus_mono (Q := ({3, 5} : Finset ℕ)) ha₀)
    have hprice : Defect S*(unitFloor (q.lower-Defect S)+
        ((q.lower-q.cutoff+1)/6).choose 2+((q.lower-q.cutoff+1)/10).choose 2) ≤
        Defect S*(UnitBound (MaxAPSize S)+(MaxAPSize S/6).choose 2+(MaxAPSize S/10).choose 2) := by
      simpa only [add_assoc] using Nat.mul_le_mul_left (Defect S) (Nat.add_le_add hu hb)
    have hi : Defect S-q.defect ∈ Finset.range (q.cutoff-q.defect) :=
      Finset.mem_range.mpr (by omega)
    have hcert := hq.2.2.2 (Defect S-q.defect) hi
    have he' : q.defect+(Defect S-q.defect) = Defect S := by omega
    rw [he'] at hcert
    exact hcert.trans (hprice.trans hstar)

#print axioms actual_plan_source
end
end JSP233.CorrelatedSource130000
