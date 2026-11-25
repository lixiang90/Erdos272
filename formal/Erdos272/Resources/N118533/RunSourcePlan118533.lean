module

public import Erdos272.Arithmetic.N291012.SourceFloorSound291012
public import Erdos272.Arithmetic.FastSource208

@[expose] public section

namespace JSP233.RunSource118533
open FastSource208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def J (s e h q : ℕ) : ℕ :=
  if q < h then fastMultiplicity s q else
    min (fastMultiplicity s q) ((s-e-q)*fastMultiplicity s h/(s-e-h))

def point (s e h : ℕ) : ℕ :=
  s.choose 3-∑ q ∈ Finset.Ico 2 (s-e), FastDecode208.phi q*J s e h q

structure Plan where
  lower : ℕ
  defect : ℕ
  target : ℕ
  upper : ℕ
  heads : List ℕ
  deriving DecidableEq

def Conditions (q : Plan) : Prop :=
  q.defect ≤ q.lower ∧ q.lower < q.upper ∧ q.upper ≤ 32754 ∧
  q.heads.length = q.upper-q.lower ∧
  ∀ i ∈ Finset.range q.heads.length,
    q.lower+i < q.defect+2 ∨
      (1 ≤ q.heads[i]! ∧ q.heads[i]! < q.lower+i-q.defect ∧
        q.target ≤ point (q.lower+i) q.defect q.heads[i]!)

instance (q : Plan) : Decidable (Conditions q) := by unfold Conditions; infer_instance

end
end JSP233.RunSource118533
