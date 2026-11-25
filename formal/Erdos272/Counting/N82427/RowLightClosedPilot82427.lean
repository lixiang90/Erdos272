module

public import Erdos272.Arithmetic.N82427.RowLightData82427
public import Erdos272.Arithmetic.N82427.ClassFastNumeric82427

@[expose] public section

namespace JSP233.RowLightClosedPilot82427
open RowLightSlope82427 PhaseSlope82427 PhaseRampSlope82427 ActualCleanupEval208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem closed_classes32 : ∀ b : CrossBandCredit208.Band, ∀ t ∈ terms 32 b,
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p ((row 32).low/(t.q*(t.q+1))) t.count=true := by
  decide +kernel
#print axioms closed_classes32

theorem closed_ramps32 : ∀ b : CrossBandCredit208.Band, ∀ t ∈ ramps 32 b,
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p
        (RampLength (row 32).low (At (row 32) (length (k:=32) (by decide)) b) t.p)
        t.count=true := by
  decide +kernel
#print axioms closed_ramps32

end
end JSP233.RowLightClosedPilot82427
