module

public import Erdos272.Core.N200000.QuantitativeUnit200000
public import Erdos272.Arithmetic.N291012.SourceFloorSound291012

@[expose] public section

namespace JSP233.MixedCore200000
open StarCompletion SourceBridge208 IntrinsicTriples208
open CoreUnionSource200000 QuantitativeUnit200000 SourceFloorSound291012
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem core_floor_split {a t u : ℕ} (hta : t ≤ a) (hcap : a ≤ 2^18)
    (ht : 9 ≤ t) (hfirst : 4*u+18*t ≤ t*t) (htail : 4*u+38*257 ≤ 257*257) :
    u ≤ UnitBound a := by
  by_cases hsmall : a ≤ 256
  · exact unit_floor (k := 8) hta hsmall ht hfirst
  · exact unit_floor (t := 257) (k := 18) (by omega) hcap (by decide) htail

theorem core_floor_large {a t u : ℕ} (hta : t ≤ a) (hcap : a ≤ 2^18)
    (ht : 19 ≤ t) (hvalue : 4*u+38*t ≤ t*t) : u ≤ UnitBound a :=
  unit_floor (k := 18) hta hcap ht hvalue

theorem actual_mixed_source {N T E D target u : ℕ} {S : Finset ℤ}
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : T ≤ S.card) (hdefect : E ≤ Defect S) (hD : D ≤ T)
    (hfloor : Floor T D target)
    (hcore : ∀ a, T-D+1 ≤ a → a ≤ 2^18 → u ≤ UnitBound a)
    (hpay : target ≤ E*u) : target ≤ (Pool S).card := by
  have hcard : S.card ≤ N := by
    simpa only [ground_card] using Finset.card_le_card hground
  by_cases hlarge : D ≤ Defect S
  · exact (hfloor S.card hsize (by norm_num at *; omega)).trans
      (actual_source_of_defect hS hlarge)
  · have hmax := maxAPSize_le_card S
    have hcorelen : T-D+1 ≤ MaxAPSize S := by
      unfold Defect at hlarge
      omega
    have hu := hcore (MaxAPSize S) hcorelen (hmax.trans (hcard.trans hN))
    exact hpay.trans ((Nat.mul_le_mul hdefect hu).trans (actual_union_core_source hS))

theorem crooked_defect_positive {S : Finset ℤ} (hS : 2 ≤ S.card) (hbad : ¬IsAP S) :
    1 ≤ Defect S := by
  obtain ⟨P, d, p, hd, hPS, hcard, hP, hAt, hgrid⟩ :=
    ActualCorePairs200000.actual_source_core hS
  by_contra hnot
  have hmax := maxAPSize_le_card S
  have he : P.card = S.card := by unfold Defect at hnot; omega
  have hsame : P = S := Finset.eq_of_subset_of_card_le hPS he.ge
  exact hbad (hsame ▸ hP.2.1)

structure Plan where
  lower : ℕ
  defect : ℕ
  target : ℕ
  cutoff : ℕ
  unit : ℕ
  deriving DecidableEq

def Conditions (q : Plan) : Prop :=
  q.cutoff ≤ q.lower ∧
  ((q.unit = 0 ∧ q.cutoff = q.defect) ∨
    (q.target ≤ q.defect*q.unit ∧
      ((9 ≤ q.lower-q.cutoff+1 ∧
        4*q.unit+18*(q.lower-q.cutoff+1) ≤ (q.lower-q.cutoff+1)^2 ∧
        4*q.unit+38*257 ≤ 257*257) ∨
       (19 ≤ q.lower-q.cutoff+1 ∧
        4*q.unit+38*(q.lower-q.cutoff+1) ≤ (q.lower-q.cutoff+1)^2))))

instance (q : Plan) : Decidable (Conditions q) := by unfold Conditions; infer_instance

theorem actual_plan_source {N : ℕ} {S : Finset ℤ} (q : Plan)
    (hq : Conditions q) (hf : Floor q.lower q.cutoff q.target)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : q.lower ≤ S.card) (hdefect : q.defect ≤ Defect S) :
    q.target ≤ (Pool S).card := by
  rcases hq.2 with hlegacy | hmixed
  · have hcard : S.card ≤ N := by
      simpa only [ground_card] using Finset.card_le_card hground
    exact (hf S.card hsize (by norm_num at *; omega)).trans
      (actual_source_of_defect hS (by simpa only [hlegacy.2] using hdefect))
  · apply actual_mixed_source hN hground hS hsize hdefect hq.1 hf _ hmixed.1
    intro a hlow hcap
    rcases hmixed.2 with hsmall | hlarge
    · exact core_floor_split hlow hcap hsmall.1 (by simpa only [pow_two] using hsmall.2.1) hsmall.2.2
    · exact core_floor_large hlow hcap hlarge.1 (by simpa only [pow_two] using hlarge.2)

#print axioms core_floor_split
#print axioms core_floor_large
#print axioms actual_mixed_source
#print axioms crooked_defect_positive
#print axioms actual_plan_source
end
end JSP233.MixedCore200000
