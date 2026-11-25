module

public import Erdos272.Arithmetic.N82427.RowLightData82427

@[expose] public section

namespace JSP233.RowLightChecks82427G00
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

theorem facts00 (b : CrossBandCredit208.Band) :
    BandFacts (row 0).high (CleanupRows82427.data 0).steps (At (row 0) (length (by decide)) b) (terms 0 b) ∧
    RampFacts (row 0).high (CleanupRows82427.data 0).steps (At (row 0) (length (by decide)) b) (ramps 0 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts00

theorem slope00 : PhaseRampSlope82427.RowSlope (row 0) (length (by decide))
    (terms 0) (ramps 0)=slope 0 := by decide +kernel
#print axioms slope00

theorem facts01 (b : CrossBandCredit208.Band) :
    BandFacts (row 1).high (CleanupRows82427.data 1).steps (At (row 1) (length (by decide)) b) (terms 1 b) ∧
    RampFacts (row 1).high (CleanupRows82427.data 1).steps (At (row 1) (length (by decide)) b) (ramps 1 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts01

theorem slope01 : PhaseRampSlope82427.RowSlope (row 1) (length (by decide))
    (terms 1) (ramps 1)=slope 1 := by decide +kernel
#print axioms slope01

theorem facts02 (b : CrossBandCredit208.Band) :
    BandFacts (row 2).high (CleanupRows82427.data 2).steps (At (row 2) (length (by decide)) b) (terms 2 b) ∧
    RampFacts (row 2).high (CleanupRows82427.data 2).steps (At (row 2) (length (by decide)) b) (ramps 2 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts02

theorem slope02 : PhaseRampSlope82427.RowSlope (row 2) (length (by decide))
    (terms 2) (ramps 2)=slope 2 := by decide +kernel
#print axioms slope02

theorem facts03 (b : CrossBandCredit208.Band) :
    BandFacts (row 3).high (CleanupRows82427.data 3).steps (At (row 3) (length (by decide)) b) (terms 3 b) ∧
    RampFacts (row 3).high (CleanupRows82427.data 3).steps (At (row 3) (length (by decide)) b) (ramps 3 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts03

theorem slope03 : PhaseRampSlope82427.RowSlope (row 3) (length (by decide))
    (terms 3) (ramps 3)=slope 3 := by decide +kernel
#print axioms slope03

theorem facts04 (b : CrossBandCredit208.Band) :
    BandFacts (row 4).high (CleanupRows82427.data 4).steps (At (row 4) (length (by decide)) b) (terms 4 b) ∧
    RampFacts (row 4).high (CleanupRows82427.data 4).steps (At (row 4) (length (by decide)) b) (ramps 4 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts04

theorem slope04 : PhaseRampSlope82427.RowSlope (row 4) (length (by decide))
    (terms 4) (ramps 4)=slope 4 := by decide +kernel
#print axioms slope04

theorem facts05 (b : CrossBandCredit208.Band) :
    BandFacts (row 5).high (CleanupRows82427.data 5).steps (At (row 5) (length (by decide)) b) (terms 5 b) ∧
    RampFacts (row 5).high (CleanupRows82427.data 5).steps (At (row 5) (length (by decide)) b) (ramps 5 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts05

theorem slope05 : PhaseRampSlope82427.RowSlope (row 5) (length (by decide))
    (terms 5) (ramps 5)=slope 5 := by decide +kernel
#print axioms slope05

theorem facts06 (b : CrossBandCredit208.Band) :
    BandFacts (row 6).high (CleanupRows82427.data 6).steps (At (row 6) (length (by decide)) b) (terms 6 b) ∧
    RampFacts (row 6).high (CleanupRows82427.data 6).steps (At (row 6) (length (by decide)) b) (ramps 6 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts06

theorem slope06 : PhaseRampSlope82427.RowSlope (row 6) (length (by decide))
    (terms 6) (ramps 6)=slope 6 := by decide +kernel
#print axioms slope06

theorem facts07 (b : CrossBandCredit208.Band) :
    BandFacts (row 7).high (CleanupRows82427.data 7).steps (At (row 7) (length (by decide)) b) (terms 7 b) ∧
    RampFacts (row 7).high (CleanupRows82427.data 7).steps (At (row 7) (length (by decide)) b) (ramps 7 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts07

theorem slope07 : PhaseRampSlope82427.RowSlope (row 7) (length (by decide))
    (terms 7) (ramps 7)=slope 7 := by decide +kernel
#print axioms slope07

theorem facts08 (b : CrossBandCredit208.Band) :
    BandFacts (row 8).high (CleanupRows82427.data 8).steps (At (row 8) (length (by decide)) b) (terms 8 b) ∧
    RampFacts (row 8).high (CleanupRows82427.data 8).steps (At (row 8) (length (by decide)) b) (ramps 8 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts08

theorem slope08 : PhaseRampSlope82427.RowSlope (row 8) (length (by decide))
    (terms 8) (ramps 8)=slope 8 := by decide +kernel
#print axioms slope08

theorem facts09 (b : CrossBandCredit208.Band) :
    BandFacts (row 9).high (CleanupRows82427.data 9).steps (At (row 9) (length (by decide)) b) (terms 9 b) ∧
    RampFacts (row 9).high (CleanupRows82427.data 9).steps (At (row 9) (length (by decide)) b) (ramps 9 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts09

theorem slope09 : PhaseRampSlope82427.RowSlope (row 9) (length (by decide))
    (terms 9) (ramps 9)=slope 9 := by decide +kernel
#print axioms slope09

theorem facts10 (b : CrossBandCredit208.Band) :
    BandFacts (row 10).high (CleanupRows82427.data 10).steps (At (row 10) (length (by decide)) b) (terms 10 b) ∧
    RampFacts (row 10).high (CleanupRows82427.data 10).steps (At (row 10) (length (by decide)) b) (ramps 10 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts10

theorem slope10 : PhaseRampSlope82427.RowSlope (row 10) (length (by decide))
    (terms 10) (ramps 10)=slope 10 := by decide +kernel
#print axioms slope10

theorem facts11 (b : CrossBandCredit208.Band) :
    BandFacts (row 11).high (CleanupRows82427.data 11).steps (At (row 11) (length (by decide)) b) (terms 11 b) ∧
    RampFacts (row 11).high (CleanupRows82427.data 11).steps (At (row 11) (length (by decide)) b) (ramps 11 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts11

theorem slope11 : PhaseRampSlope82427.RowSlope (row 11) (length (by decide))
    (terms 11) (ramps 11)=slope 11 := by decide +kernel
#print axioms slope11

theorem facts12 (b : CrossBandCredit208.Band) :
    BandFacts (row 12).high (CleanupRows82427.data 12).steps (At (row 12) (length (by decide)) b) (terms 12 b) ∧
    RampFacts (row 12).high (CleanupRows82427.data 12).steps (At (row 12) (length (by decide)) b) (ramps 12 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts12

theorem slope12 : PhaseRampSlope82427.RowSlope (row 12) (length (by decide))
    (terms 12) (ramps 12)=slope 12 := by decide +kernel
#print axioms slope12

theorem facts13 (b : CrossBandCredit208.Band) :
    BandFacts (row 13).high (CleanupRows82427.data 13).steps (At (row 13) (length (by decide)) b) (terms 13 b) ∧
    RampFacts (row 13).high (CleanupRows82427.data 13).steps (At (row 13) (length (by decide)) b) (ramps 13 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts13

theorem slope13 : PhaseRampSlope82427.RowSlope (row 13) (length (by decide))
    (terms 13) (ramps 13)=slope 13 := by decide +kernel
#print axioms slope13

theorem facts14 (b : CrossBandCredit208.Band) :
    BandFacts (row 14).high (CleanupRows82427.data 14).steps (At (row 14) (length (by decide)) b) (terms 14 b) ∧
    RampFacts (row 14).high (CleanupRows82427.data 14).steps (At (row 14) (length (by decide)) b) (ramps 14 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts14

theorem slope14 : PhaseRampSlope82427.RowSlope (row 14) (length (by decide))
    (terms 14) (ramps 14)=slope 14 := by decide +kernel
#print axioms slope14

theorem facts15 (b : CrossBandCredit208.Band) :
    BandFacts (row 15).high (CleanupRows82427.data 15).steps (At (row 15) (length (by decide)) b) (terms 15 b) ∧
    RampFacts (row 15).high (CleanupRows82427.data 15).steps (At (row 15) (length (by decide)) b) (ramps 15 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts15

theorem slope15 : PhaseRampSlope82427.RowSlope (row 15) (length (by decide))
    (terms 15) (ramps 15)=slope 15 := by decide +kernel
#print axioms slope15

end
end JSP233.RowLightChecks82427G00
