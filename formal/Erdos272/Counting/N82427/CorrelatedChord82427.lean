module

public import Erdos272.Resources.N82427.ThreeFiveSource82427
public import Erdos272.Resources.N86412.SourceCorrelated86412

@[expose] public section

namespace JSP233.CorrelatedChord82427
open StarCompletion SourceBridge208 IntrinsicTriples208 UnitFloorData158375
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev Plan := CorrelatedSource118533.Plan

def Conditions (q : Plan) : Prop :=
  q.defect ≤ q.cutoff ∧ q.cutoff ≤ q.lower ∧ 12 ≤ q.lower-q.cutoff+1 ∧
  ∀ i ∈ Finset.range (q.cutoff-q.defect),
    q.target ≤ (q.defect+i) *
      (unitFloor (q.lower-(q.defect+i)) +
        StarArithmetic130000.Bonus CorrelatedSource118533.Primes (q.lower-(q.defect+i)) +
        ThreeFiveArithmetic82427.ChordBonus (q.lower-(q.defect+i)))

instance (q : Plan) : Decidable (Conditions q) := by
  unfold Conditions
  infer_instance

theorem actual_plan_source_of_high {N : ℕ} {S : Finset ℤ} (q : Plan)
    (hq : Conditions q)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : q.lower ≤ S.card) (hdefect : q.defect ≤ Defect S)
    (hhigh : q.cutoff ≤ Defect S → q.target ≤ (Pool S).card) :
    q.target ≤ (Pool S).card := by
  by_cases hc : q.cutoff ≤ Defect S
  · exact hhigh hc
  · have he : Defect S+MaxAPSize S=S.card := by
      unfold Defect
      exact Nat.sub_add_cancel (maxAPSize_le_card S)
    have hcut : q.cutoff ≤ q.lower := hq.2.1
    have ha₀ : q.lower-q.cutoff+1 ≤ MaxAPSize S := by omega
    have ha : 12 ≤ MaxAPSize S := hq.2.2.1.trans ha₀
    have hlower : q.lower-Defect S ≤ MaxAPSize S := by omega
    have hstar := ThreeFiveSource82427.actual_core_lower_price hN hground hS ha hlower
    have hi : Defect S-q.defect ∈ Finset.range (q.cutoff-q.defect) :=
      Finset.mem_range.mpr (by omega)
    have hcert := hq.2.2.2 (Defect S-q.defect) hi
    have he' : q.defect+(Defect S-q.defect)=Defect S := by omega
    rw [he'] at hcert
    exact hcert.trans hstar

theorem chord_paid (q : Plan) (hq : Conditions q) (high : CertifiedContract)
    (hlower : high.contract.lower ≤ q.lower) (hdefect : high.contract.defect ≤ q.cutoff)
    (htarget : q.target ≤ high.contract.target) :
    Paid (SourceCorrelated86412.ofPlan q) := by
  intro N S hN hground hS hsize hdef
  apply actual_plan_source_of_high q hq hN hground hS hsize hdef
  intro hhigh
  exact htarget.trans (high.actual hN hground hS (hlower.trans hsize) (hdefect.trans hhigh))

def chord (q : Plan) (hq : Conditions q) (high : CertifiedContract)
    (hlower : high.contract.lower ≤ q.lower) (hdefect : high.contract.defect ≤ q.cutoff)
    (htarget : q.target ≤ high.contract.target) : CertifiedContract :=
  ⟨SourceCorrelated86412.ofPlan q, chord_paid q hq high hlower hdefect htarget⟩

#print axioms actual_plan_source_of_high
#print axioms chord_paid
end
end JSP233.CorrelatedChord82427
