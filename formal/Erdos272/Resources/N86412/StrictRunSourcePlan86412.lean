module

public import Erdos272.Resources.N109474.RunSourcePlan109474

@[expose] public section

namespace JSP233.StrictRunSource86412
open FastSource208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def I (s q : ℕ) : ℕ := fastMultiplicity s q - if 3 ≤ q then 1 else 0

def J (s e h q : ℕ) : ℕ :=
  if q < h then I s q else
    min (I s q) ((s-e-q)*(I s h/(s-e-h))+(I s h%(s-e-h)-(q-h)))

def point (s e h : ℕ) : ℕ :=
  s.choose 3 - ∑ q ∈ Finset.Ico 2 (s-e), FastDecode208.phi q*J s e h q

abbrev Plan := RunSource109474.Plan

def Conditions (q : Plan) : Prop :=
  2 ≤ q.defect ∧ q.defect ≤ q.lower ∧ q.lower < q.upper ∧ q.upper ≤ 32754 ∧
  q.heads.length = q.upper-q.lower ∧
  ∀ i ∈ Finset.range q.heads.length,
    q.lower+i < q.defect+2 ∨
      (1 ≤ q.heads[i]! ∧ q.heads[i]! < q.lower+i-q.defect ∧
        q.target ≤ point (q.lower+i) q.defect q.heads[i]!)

instance (q : Plan) : Decidable (Conditions q) := by
  unfold Conditions
  infer_instance

end
end JSP233.StrictRunSource86412
