module

public import Erdos272.Arithmetic.N82427.RowLightData82427

@[expose] public section

namespace JSP233.RowLightChecks82427G05
open RowLightSlope82427 PhaseSlope82427 PhaseRampSlope82427 ActualCleanupEval208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

local instance (b : CleanupEval208.Band) : Decidable (Shape b) :=
  inferInstanceAs (Decidable (b.E ≤ b.T ∧ b.T < b.U ∧ 2 ≤ b.b2 ∧ 2 ≤ b.b3 ∧
    2 ≤ b.b5 ∧ 2 ≤ b.b7 ∧ 2 ≤ b.b11))
local instance (high D : ℕ) (b : CleanupEval208.Band) (t : Term) : Decidable (TermFacts high D b t) :=
  inferInstanceAs (Decidable (0 < t.q ∧ high/t.q ≤ D ∧
    t.q=b.T-b.E+((t.q-(b.T-b.E))/OwnerBlock b t.p)*OwnerBlock b t.p))
local instance (high D : ℕ) (b : CleanupEval208.Band) (ts : Finset Term) : Decidable (BandFacts high D b ts) :=
  inferInstanceAs (Decidable (Shape b ∧ (b.E ≤ 1 → ts=∅) ∧
    (∀ t ∈ ts, ∀ u ∈ ts, t.p=u.p → t.q=u.q → t=u) ∧ ∀ t ∈ ts, TermFacts high D b t))
local instance (high D : ℕ) (b : CleanupEval208.Band) (rs : Finset RampTerm) : Decidable (RampFacts high D b rs) :=
  inferInstanceAs (Decidable ((b.E ≤ 1 → rs=∅) ∧
    (∀ t ∈ rs, ∀ u ∈ rs, t.p=u.p → t=u) ∧
    ∀ t ∈ rs, b.E ≤ b.T ∧ b.T ≤ RampV b t.p ∧ high/RampA b ≤ D))

theorem facts80 (b : CrossBandCredit208.Band) :
    BandFacts (row 80).high (CleanupRows82427.data 80).steps (At (row 80) (length (by decide)) b) (terms 80 b) ∧
    RampFacts (row 80).high (CleanupRows82427.data 80).steps (At (row 80) (length (by decide)) b) (ramps 80 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts80

theorem slope80 : PhaseRampSlope82427.RowSlope (row 80) (length (by decide))
    (terms 80) (ramps 80)=slope 80 := by decide +kernel
#print axioms slope80

theorem facts81 (b : CrossBandCredit208.Band) :
    BandFacts (row 81).high (CleanupRows82427.data 81).steps (At (row 81) (length (by decide)) b) (terms 81 b) ∧
    RampFacts (row 81).high (CleanupRows82427.data 81).steps (At (row 81) (length (by decide)) b) (ramps 81 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts81

theorem slope81 : PhaseRampSlope82427.RowSlope (row 81) (length (by decide))
    (terms 81) (ramps 81)=slope 81 := by decide +kernel
#print axioms slope81

theorem facts82 (b : CrossBandCredit208.Band) :
    BandFacts (row 82).high (CleanupRows82427.data 82).steps (At (row 82) (length (by decide)) b) (terms 82 b) ∧
    RampFacts (row 82).high (CleanupRows82427.data 82).steps (At (row 82) (length (by decide)) b) (ramps 82 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts82

theorem slope82 : PhaseRampSlope82427.RowSlope (row 82) (length (by decide))
    (terms 82) (ramps 82)=slope 82 := by decide +kernel
#print axioms slope82

theorem facts83 (b : CrossBandCredit208.Band) :
    BandFacts (row 83).high (CleanupRows82427.data 83).steps (At (row 83) (length (by decide)) b) (terms 83 b) ∧
    RampFacts (row 83).high (CleanupRows82427.data 83).steps (At (row 83) (length (by decide)) b) (ramps 83 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts83

theorem slope83 : PhaseRampSlope82427.RowSlope (row 83) (length (by decide))
    (terms 83) (ramps 83)=slope 83 := by decide +kernel
#print axioms slope83

theorem facts84 (b : CrossBandCredit208.Band) :
    BandFacts (row 84).high (CleanupRows82427.data 84).steps (At (row 84) (length (by decide)) b) (terms 84 b) ∧
    RampFacts (row 84).high (CleanupRows82427.data 84).steps (At (row 84) (length (by decide)) b) (ramps 84 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts84

theorem slope84 : PhaseRampSlope82427.RowSlope (row 84) (length (by decide))
    (terms 84) (ramps 84)=slope 84 := by decide +kernel
#print axioms slope84

theorem facts85 (b : CrossBandCredit208.Band) :
    BandFacts (row 85).high (CleanupRows82427.data 85).steps (At (row 85) (length (by decide)) b) (terms 85 b) ∧
    RampFacts (row 85).high (CleanupRows82427.data 85).steps (At (row 85) (length (by decide)) b) (ramps 85 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts85

theorem slope85 : PhaseRampSlope82427.RowSlope (row 85) (length (by decide))
    (terms 85) (ramps 85)=slope 85 := by decide +kernel
#print axioms slope85

theorem facts86 (b : CrossBandCredit208.Band) :
    BandFacts (row 86).high (CleanupRows82427.data 86).steps (At (row 86) (length (by decide)) b) (terms 86 b) ∧
    RampFacts (row 86).high (CleanupRows82427.data 86).steps (At (row 86) (length (by decide)) b) (ramps 86 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts86

theorem slope86 : PhaseRampSlope82427.RowSlope (row 86) (length (by decide))
    (terms 86) (ramps 86)=slope 86 := by decide +kernel
#print axioms slope86

theorem facts87 (b : CrossBandCredit208.Band) :
    BandFacts (row 87).high (CleanupRows82427.data 87).steps (At (row 87) (length (by decide)) b) (terms 87 b) ∧
    RampFacts (row 87).high (CleanupRows82427.data 87).steps (At (row 87) (length (by decide)) b) (ramps 87 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts87

theorem slope87 : PhaseRampSlope82427.RowSlope (row 87) (length (by decide))
    (terms 87) (ramps 87)=slope 87 := by decide +kernel
#print axioms slope87

end
end JSP233.RowLightChecks82427G05
