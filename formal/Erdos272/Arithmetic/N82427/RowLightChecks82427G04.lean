module

public import Erdos272.Arithmetic.N82427.RowLightData82427

@[expose] public section

namespace JSP233.RowLightChecks82427G04
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

theorem facts64 (b : CrossBandCredit208.Band) :
    BandFacts (row 64).high (CleanupRows82427.data 64).steps (At (row 64) (length (by decide)) b) (terms 64 b) ∧
    RampFacts (row 64).high (CleanupRows82427.data 64).steps (At (row 64) (length (by decide)) b) (ramps 64 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts64

theorem slope64 : PhaseRampSlope82427.RowSlope (row 64) (length (by decide))
    (terms 64) (ramps 64)=slope 64 := by decide +kernel
#print axioms slope64

theorem facts65 (b : CrossBandCredit208.Band) :
    BandFacts (row 65).high (CleanupRows82427.data 65).steps (At (row 65) (length (by decide)) b) (terms 65 b) ∧
    RampFacts (row 65).high (CleanupRows82427.data 65).steps (At (row 65) (length (by decide)) b) (ramps 65 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts65

theorem slope65 : PhaseRampSlope82427.RowSlope (row 65) (length (by decide))
    (terms 65) (ramps 65)=slope 65 := by decide +kernel
#print axioms slope65

theorem facts66 (b : CrossBandCredit208.Band) :
    BandFacts (row 66).high (CleanupRows82427.data 66).steps (At (row 66) (length (by decide)) b) (terms 66 b) ∧
    RampFacts (row 66).high (CleanupRows82427.data 66).steps (At (row 66) (length (by decide)) b) (ramps 66 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts66

theorem slope66 : PhaseRampSlope82427.RowSlope (row 66) (length (by decide))
    (terms 66) (ramps 66)=slope 66 := by decide +kernel
#print axioms slope66

theorem facts67 (b : CrossBandCredit208.Band) :
    BandFacts (row 67).high (CleanupRows82427.data 67).steps (At (row 67) (length (by decide)) b) (terms 67 b) ∧
    RampFacts (row 67).high (CleanupRows82427.data 67).steps (At (row 67) (length (by decide)) b) (ramps 67 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts67

theorem slope67 : PhaseRampSlope82427.RowSlope (row 67) (length (by decide))
    (terms 67) (ramps 67)=slope 67 := by decide +kernel
#print axioms slope67

theorem facts68 (b : CrossBandCredit208.Band) :
    BandFacts (row 68).high (CleanupRows82427.data 68).steps (At (row 68) (length (by decide)) b) (terms 68 b) ∧
    RampFacts (row 68).high (CleanupRows82427.data 68).steps (At (row 68) (length (by decide)) b) (ramps 68 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts68

theorem slope68 : PhaseRampSlope82427.RowSlope (row 68) (length (by decide))
    (terms 68) (ramps 68)=slope 68 := by decide +kernel
#print axioms slope68

theorem facts69 (b : CrossBandCredit208.Band) :
    BandFacts (row 69).high (CleanupRows82427.data 69).steps (At (row 69) (length (by decide)) b) (terms 69 b) ∧
    RampFacts (row 69).high (CleanupRows82427.data 69).steps (At (row 69) (length (by decide)) b) (ramps 69 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts69

theorem slope69 : PhaseRampSlope82427.RowSlope (row 69) (length (by decide))
    (terms 69) (ramps 69)=slope 69 := by decide +kernel
#print axioms slope69

theorem facts70 (b : CrossBandCredit208.Band) :
    BandFacts (row 70).high (CleanupRows82427.data 70).steps (At (row 70) (length (by decide)) b) (terms 70 b) ∧
    RampFacts (row 70).high (CleanupRows82427.data 70).steps (At (row 70) (length (by decide)) b) (ramps 70 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts70

theorem slope70 : PhaseRampSlope82427.RowSlope (row 70) (length (by decide))
    (terms 70) (ramps 70)=slope 70 := by decide +kernel
#print axioms slope70

theorem facts71 (b : CrossBandCredit208.Band) :
    BandFacts (row 71).high (CleanupRows82427.data 71).steps (At (row 71) (length (by decide)) b) (terms 71 b) ∧
    RampFacts (row 71).high (CleanupRows82427.data 71).steps (At (row 71) (length (by decide)) b) (ramps 71 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts71

theorem slope71 : PhaseRampSlope82427.RowSlope (row 71) (length (by decide))
    (terms 71) (ramps 71)=slope 71 := by decide +kernel
#print axioms slope71

theorem facts72 (b : CrossBandCredit208.Band) :
    BandFacts (row 72).high (CleanupRows82427.data 72).steps (At (row 72) (length (by decide)) b) (terms 72 b) ∧
    RampFacts (row 72).high (CleanupRows82427.data 72).steps (At (row 72) (length (by decide)) b) (ramps 72 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts72

theorem slope72 : PhaseRampSlope82427.RowSlope (row 72) (length (by decide))
    (terms 72) (ramps 72)=slope 72 := by decide +kernel
#print axioms slope72

theorem facts73 (b : CrossBandCredit208.Band) :
    BandFacts (row 73).high (CleanupRows82427.data 73).steps (At (row 73) (length (by decide)) b) (terms 73 b) ∧
    RampFacts (row 73).high (CleanupRows82427.data 73).steps (At (row 73) (length (by decide)) b) (ramps 73 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts73

theorem slope73 : PhaseRampSlope82427.RowSlope (row 73) (length (by decide))
    (terms 73) (ramps 73)=slope 73 := by decide +kernel
#print axioms slope73

theorem facts74 (b : CrossBandCredit208.Band) :
    BandFacts (row 74).high (CleanupRows82427.data 74).steps (At (row 74) (length (by decide)) b) (terms 74 b) ∧
    RampFacts (row 74).high (CleanupRows82427.data 74).steps (At (row 74) (length (by decide)) b) (ramps 74 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts74

theorem slope74 : PhaseRampSlope82427.RowSlope (row 74) (length (by decide))
    (terms 74) (ramps 74)=slope 74 := by decide +kernel
#print axioms slope74

theorem facts75 (b : CrossBandCredit208.Band) :
    BandFacts (row 75).high (CleanupRows82427.data 75).steps (At (row 75) (length (by decide)) b) (terms 75 b) ∧
    RampFacts (row 75).high (CleanupRows82427.data 75).steps (At (row 75) (length (by decide)) b) (ramps 75 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts75

theorem slope75 : PhaseRampSlope82427.RowSlope (row 75) (length (by decide))
    (terms 75) (ramps 75)=slope 75 := by decide +kernel
#print axioms slope75

theorem facts76 (b : CrossBandCredit208.Band) :
    BandFacts (row 76).high (CleanupRows82427.data 76).steps (At (row 76) (length (by decide)) b) (terms 76 b) ∧
    RampFacts (row 76).high (CleanupRows82427.data 76).steps (At (row 76) (length (by decide)) b) (ramps 76 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts76

theorem slope76 : PhaseRampSlope82427.RowSlope (row 76) (length (by decide))
    (terms 76) (ramps 76)=slope 76 := by decide +kernel
#print axioms slope76

theorem facts77 (b : CrossBandCredit208.Band) :
    BandFacts (row 77).high (CleanupRows82427.data 77).steps (At (row 77) (length (by decide)) b) (terms 77 b) ∧
    RampFacts (row 77).high (CleanupRows82427.data 77).steps (At (row 77) (length (by decide)) b) (ramps 77 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts77

theorem slope77 : PhaseRampSlope82427.RowSlope (row 77) (length (by decide))
    (terms 77) (ramps 77)=slope 77 := by decide +kernel
#print axioms slope77

theorem facts78 (b : CrossBandCredit208.Band) :
    BandFacts (row 78).high (CleanupRows82427.data 78).steps (At (row 78) (length (by decide)) b) (terms 78 b) ∧
    RampFacts (row 78).high (CleanupRows82427.data 78).steps (At (row 78) (length (by decide)) b) (ramps 78 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts78

theorem slope78 : PhaseRampSlope82427.RowSlope (row 78) (length (by decide))
    (terms 78) (ramps 78)=slope 78 := by decide +kernel
#print axioms slope78

theorem facts79 (b : CrossBandCredit208.Band) :
    BandFacts (row 79).high (CleanupRows82427.data 79).steps (At (row 79) (length (by decide)) b) (terms 79 b) ∧
    RampFacts (row 79).high (CleanupRows82427.data 79).steps (At (row 79) (length (by decide)) b) (ramps 79 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts79

theorem slope79 : PhaseRampSlope82427.RowSlope (row 79) (length (by decide))
    (terms 79) (ramps 79)=slope 79 := by decide +kernel
#print axioms slope79

end
end JSP233.RowLightChecks82427G04
