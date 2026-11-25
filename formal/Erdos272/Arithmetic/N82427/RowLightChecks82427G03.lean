module

public import Erdos272.Arithmetic.N82427.RowLightData82427

@[expose] public section

namespace JSP233.RowLightChecks82427G03
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

theorem facts48 (b : CrossBandCredit208.Band) :
    BandFacts (row 48).high (CleanupRows82427.data 48).steps (At (row 48) (length (by decide)) b) (terms 48 b) ∧
    RampFacts (row 48).high (CleanupRows82427.data 48).steps (At (row 48) (length (by decide)) b) (ramps 48 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts48

theorem slope48 : PhaseRampSlope82427.RowSlope (row 48) (length (by decide))
    (terms 48) (ramps 48)=slope 48 := by decide +kernel
#print axioms slope48

theorem facts49 (b : CrossBandCredit208.Band) :
    BandFacts (row 49).high (CleanupRows82427.data 49).steps (At (row 49) (length (by decide)) b) (terms 49 b) ∧
    RampFacts (row 49).high (CleanupRows82427.data 49).steps (At (row 49) (length (by decide)) b) (ramps 49 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts49

theorem slope49 : PhaseRampSlope82427.RowSlope (row 49) (length (by decide))
    (terms 49) (ramps 49)=slope 49 := by decide +kernel
#print axioms slope49

theorem facts50 (b : CrossBandCredit208.Band) :
    BandFacts (row 50).high (CleanupRows82427.data 50).steps (At (row 50) (length (by decide)) b) (terms 50 b) ∧
    RampFacts (row 50).high (CleanupRows82427.data 50).steps (At (row 50) (length (by decide)) b) (ramps 50 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts50

theorem slope50 : PhaseRampSlope82427.RowSlope (row 50) (length (by decide))
    (terms 50) (ramps 50)=slope 50 := by decide +kernel
#print axioms slope50

theorem facts51 (b : CrossBandCredit208.Band) :
    BandFacts (row 51).high (CleanupRows82427.data 51).steps (At (row 51) (length (by decide)) b) (terms 51 b) ∧
    RampFacts (row 51).high (CleanupRows82427.data 51).steps (At (row 51) (length (by decide)) b) (ramps 51 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts51

theorem slope51 : PhaseRampSlope82427.RowSlope (row 51) (length (by decide))
    (terms 51) (ramps 51)=slope 51 := by decide +kernel
#print axioms slope51

theorem facts52 (b : CrossBandCredit208.Band) :
    BandFacts (row 52).high (CleanupRows82427.data 52).steps (At (row 52) (length (by decide)) b) (terms 52 b) ∧
    RampFacts (row 52).high (CleanupRows82427.data 52).steps (At (row 52) (length (by decide)) b) (ramps 52 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts52

theorem slope52 : PhaseRampSlope82427.RowSlope (row 52) (length (by decide))
    (terms 52) (ramps 52)=slope 52 := by decide +kernel
#print axioms slope52

theorem facts53 (b : CrossBandCredit208.Band) :
    BandFacts (row 53).high (CleanupRows82427.data 53).steps (At (row 53) (length (by decide)) b) (terms 53 b) ∧
    RampFacts (row 53).high (CleanupRows82427.data 53).steps (At (row 53) (length (by decide)) b) (ramps 53 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts53

theorem slope53 : PhaseRampSlope82427.RowSlope (row 53) (length (by decide))
    (terms 53) (ramps 53)=slope 53 := by decide +kernel
#print axioms slope53

theorem facts54 (b : CrossBandCredit208.Band) :
    BandFacts (row 54).high (CleanupRows82427.data 54).steps (At (row 54) (length (by decide)) b) (terms 54 b) ∧
    RampFacts (row 54).high (CleanupRows82427.data 54).steps (At (row 54) (length (by decide)) b) (ramps 54 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts54

theorem slope54 : PhaseRampSlope82427.RowSlope (row 54) (length (by decide))
    (terms 54) (ramps 54)=slope 54 := by decide +kernel
#print axioms slope54

theorem facts55 (b : CrossBandCredit208.Band) :
    BandFacts (row 55).high (CleanupRows82427.data 55).steps (At (row 55) (length (by decide)) b) (terms 55 b) ∧
    RampFacts (row 55).high (CleanupRows82427.data 55).steps (At (row 55) (length (by decide)) b) (ramps 55 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts55

theorem slope55 : PhaseRampSlope82427.RowSlope (row 55) (length (by decide))
    (terms 55) (ramps 55)=slope 55 := by decide +kernel
#print axioms slope55

theorem facts56 (b : CrossBandCredit208.Band) :
    BandFacts (row 56).high (CleanupRows82427.data 56).steps (At (row 56) (length (by decide)) b) (terms 56 b) ∧
    RampFacts (row 56).high (CleanupRows82427.data 56).steps (At (row 56) (length (by decide)) b) (ramps 56 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts56

theorem slope56 : PhaseRampSlope82427.RowSlope (row 56) (length (by decide))
    (terms 56) (ramps 56)=slope 56 := by decide +kernel
#print axioms slope56

theorem facts57 (b : CrossBandCredit208.Band) :
    BandFacts (row 57).high (CleanupRows82427.data 57).steps (At (row 57) (length (by decide)) b) (terms 57 b) ∧
    RampFacts (row 57).high (CleanupRows82427.data 57).steps (At (row 57) (length (by decide)) b) (ramps 57 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts57

theorem slope57 : PhaseRampSlope82427.RowSlope (row 57) (length (by decide))
    (terms 57) (ramps 57)=slope 57 := by decide +kernel
#print axioms slope57

theorem facts58 (b : CrossBandCredit208.Band) :
    BandFacts (row 58).high (CleanupRows82427.data 58).steps (At (row 58) (length (by decide)) b) (terms 58 b) ∧
    RampFacts (row 58).high (CleanupRows82427.data 58).steps (At (row 58) (length (by decide)) b) (ramps 58 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts58

theorem slope58 : PhaseRampSlope82427.RowSlope (row 58) (length (by decide))
    (terms 58) (ramps 58)=slope 58 := by decide +kernel
#print axioms slope58

theorem facts59 (b : CrossBandCredit208.Band) :
    BandFacts (row 59).high (CleanupRows82427.data 59).steps (At (row 59) (length (by decide)) b) (terms 59 b) ∧
    RampFacts (row 59).high (CleanupRows82427.data 59).steps (At (row 59) (length (by decide)) b) (ramps 59 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts59

theorem slope59 : PhaseRampSlope82427.RowSlope (row 59) (length (by decide))
    (terms 59) (ramps 59)=slope 59 := by decide +kernel
#print axioms slope59

theorem facts60 (b : CrossBandCredit208.Band) :
    BandFacts (row 60).high (CleanupRows82427.data 60).steps (At (row 60) (length (by decide)) b) (terms 60 b) ∧
    RampFacts (row 60).high (CleanupRows82427.data 60).steps (At (row 60) (length (by decide)) b) (ramps 60 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts60

theorem slope60 : PhaseRampSlope82427.RowSlope (row 60) (length (by decide))
    (terms 60) (ramps 60)=slope 60 := by decide +kernel
#print axioms slope60

theorem facts61 (b : CrossBandCredit208.Band) :
    BandFacts (row 61).high (CleanupRows82427.data 61).steps (At (row 61) (length (by decide)) b) (terms 61 b) ∧
    RampFacts (row 61).high (CleanupRows82427.data 61).steps (At (row 61) (length (by decide)) b) (ramps 61 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts61

theorem slope61 : PhaseRampSlope82427.RowSlope (row 61) (length (by decide))
    (terms 61) (ramps 61)=slope 61 := by decide +kernel
#print axioms slope61

theorem facts62 (b : CrossBandCredit208.Band) :
    BandFacts (row 62).high (CleanupRows82427.data 62).steps (At (row 62) (length (by decide)) b) (terms 62 b) ∧
    RampFacts (row 62).high (CleanupRows82427.data 62).steps (At (row 62) (length (by decide)) b) (ramps 62 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts62

theorem slope62 : PhaseRampSlope82427.RowSlope (row 62) (length (by decide))
    (terms 62) (ramps 62)=slope 62 := by decide +kernel
#print axioms slope62

theorem facts63 (b : CrossBandCredit208.Band) :
    BandFacts (row 63).high (CleanupRows82427.data 63).steps (At (row 63) (length (by decide)) b) (terms 63 b) ∧
    RampFacts (row 63).high (CleanupRows82427.data 63).steps (At (row 63) (length (by decide)) b) (ramps 63 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts63

theorem slope63 : PhaseRampSlope82427.RowSlope (row 63) (length (by decide))
    (terms 63) (ramps 63)=slope 63 := by decide +kernel
#print axioms slope63

end
end JSP233.RowLightChecks82427G03
