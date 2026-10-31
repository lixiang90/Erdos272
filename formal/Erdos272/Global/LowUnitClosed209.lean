import Erdos272.Global.LowUnitTruncated209
import Erdos272.Arithmetic.Cap150UnitRowsChecked209

namespace JSP233.LowUnitClosed209
open StarCompletion APGeometry
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 200000

/-- The actual finite interval with all 150 cleanup facts instantiated by
ordinary-kernel certificates. The hypotheses are only the interval and Legal. -/
theorem actual_original_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhi : N≤62443451) (hF : Legal (Ground N) F) : F.card≤B N := by
  apply LowUnitTruncated209.actual_joined_upper hN hhi hF
  intro k hk
  simpa only [ActualUnitFees208.Facts242] using Cap150UnitRowsChecked209.checked242 k hk

#print axioms actual_original_upper
end
end JSP233.LowUnitClosed209
