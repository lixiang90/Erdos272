module

public import Erdos272.Arithmetic.FastDecode208
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace JSP233.UniformEval86412
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def value (s : ℕ) : ℕ :=
  ∑ q ∈ Finset.Ico 3 s, if ¬q ∣ s then FastDecode208.phi q else 0

structure Plan where
  lower : ℕ
  target : ℕ
  deriving DecidableEq

end JSP233.UniformEval86412
