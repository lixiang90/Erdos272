module

public import Erdos272.Arithmetic.N67702.SourceAtlasData67702

@[expose] public section

namespace JSP233.SourceAtlasChecks67702G1
open SourceAtlasData67702
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem reference_piece {i : ℕ} (hlo : 16 ≤ i) (hhi : i < 32) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece

end
end JSP233.SourceAtlasChecks67702G1
