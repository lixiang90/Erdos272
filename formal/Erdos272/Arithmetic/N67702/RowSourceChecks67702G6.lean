module

public import Erdos272.Arithmetic.N67702.RowSourceData67702

@[expose] public section

namespace JSP233.RowSourceChecks67702G6
open RowSourceData67702
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem links {k : ℕ} (hlo : 96 ≤ k) (hhi : k < 112) (b : Fin 7) : Links k b := by
  interval_cases k <;> fin_cases b <;> unfold Links <;> decide +kernel
#print axioms links
end
end JSP233.RowSourceChecks67702G6
