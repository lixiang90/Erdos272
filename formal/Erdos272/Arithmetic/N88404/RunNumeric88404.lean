module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace JSP233.RunNumeric88404
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def phiValues : List ℕ := [0, 1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8, 12, 10, 22, 8, 20, 12, 18, 12, 28, 8, 30, 16, 20, 16, 24, 12, 36, 18, 24, 16, 40, 12, 42, 20, 24, 22, 46, 16, 42, 20, 32, 24, 52, 18, 40, 24, 36, 28, 58, 16, 60, 30, 36, 32, 48, 20, 66, 32, 44, 24, 70, 24, 72, 36, 40, 36, 60, 24, 78, 32, 54, 40, 82, 24, 64, 42, 56, 40, 88, 24, 72, 44, 60, 46, 72, 32, 96, 42, 60, 40, 100, 32, 102, 48, 48, 52, 106, 36, 108, 40, 72, 48, 112, 36, 88, 56, 72, 58, 96, 32, 110, 60, 80, 60, 100, 36, 126]

def phi (n : ℕ) : ℕ := (phiValues[n]?).getD 0

def multiplicity (s q : ℕ) : ℕ :=
  if q = 0 then s*s else
    (2*(s/q)*s-q*(s/q)*(s/q+1))/2

def J (s e h q : ℕ) : ℕ :=
  if q < h then multiplicity s q else
    min (multiplicity s q)
      ((s-e-q)*(multiplicity s h/(s-e-h))+(multiplicity s h%(s-e-h)-(q-h)))

def point (s e h : ℕ) : ℕ :=
  s.choose 3-∑ q ∈ Finset.Ico 2 (s-e), phi q*J s e h q

structure Plan where
  lower : ℕ
  defect : ℕ
  target : ℕ
  upper : ℕ
  heads : List ℕ
  deriving DecidableEq

def Conditions (q : Plan) : Prop :=
  q.upper-q.defect ≤ 129 ∧
  q.defect ≤ q.lower ∧ q.lower < q.upper ∧ q.upper ≤ 32754 ∧
  q.heads.length = q.upper-q.lower ∧
  ∀ i ∈ Finset.range q.heads.length,
    q.lower+i < q.defect+2 ∨
      (1 ≤ q.heads[i]! ∧ q.heads[i]! < q.lower+i-q.defect ∧
        q.target ≤ point (q.lower+i) q.defect q.heads[i]!)

instance (q : Plan) : Decidable (Conditions q) := by
  unfold Conditions
  infer_instance

end JSP233.RunNumeric88404
