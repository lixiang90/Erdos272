module

public import Erdos272.Arithmetic.N67702.SourceAtlasData67702

@[expose] public section

namespace JSP233.SourceAtlasChecks67702G16
open SourceAtlasData67702
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem reference_piece {i : ℕ} (hlo : 256 ≤ i) (hhi : i < 272) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece

end
end JSP233.SourceAtlasChecks67702G16
