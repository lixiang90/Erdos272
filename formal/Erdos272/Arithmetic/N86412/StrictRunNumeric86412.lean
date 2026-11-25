module

public import Erdos272.Arithmetic.N88404.RunNumeric88404

@[expose] public section

namespace JSP233.StrictRunNumeric86412
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def I (s q : ℕ) : ℕ :=
  RunNumeric88404.multiplicity s q - if 3 ≤ q then 1 else 0

def J (s e h q : ℕ) : ℕ :=
  if q < h then I s q else
    min (I s q) ((s-e-q)*(I s h/(s-e-h))+(I s h%(s-e-h)-(q-h)))

def point (s e h : ℕ) : ℕ :=
  s.choose 3 - ∑ q ∈ Finset.Ico 2 (s-e), RunNumeric88404.phi q*J s e h q

abbrev Plan := RunNumeric88404.Plan

def Conditions (q : Plan) : Prop :=
  q.upper-q.defect ≤ 129 ∧ 2 ≤ q.defect ∧
  q.defect ≤ q.lower ∧ q.lower < q.upper ∧ q.upper ≤ 32754 ∧
  q.heads.length = q.upper-q.lower ∧
  ∀ i ∈ Finset.range q.heads.length,
    q.lower+i < q.defect+2 ∨
      (1 ≤ q.heads[i]! ∧ q.heads[i]! < q.lower+i-q.defect ∧
        q.target ≤ point (q.lower+i) q.defect q.heads[i]!)

instance (q : Plan) : Decidable (Conditions q) := by
  unfold Conditions
  infer_instance

end JSP233.StrictRunNumeric86412
