module

public import Erdos272.Arithmetic.N82427.RowLightData82427

@[expose] public section

namespace JSP233.RowLightChecks82427G01
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

theorem facts16 (b : CrossBandCredit208.Band) :
    BandFacts (row 16).high (CleanupRows82427.data 16).steps (At (row 16) (length (by decide)) b) (terms 16 b) ∧
    RampFacts (row 16).high (CleanupRows82427.data 16).steps (At (row 16) (length (by decide)) b) (ramps 16 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts16

theorem slope16 : PhaseRampSlope82427.RowSlope (row 16) (length (by decide))
    (terms 16) (ramps 16)=slope 16 := by decide +kernel
#print axioms slope16

theorem facts17 (b : CrossBandCredit208.Band) :
    BandFacts (row 17).high (CleanupRows82427.data 17).steps (At (row 17) (length (by decide)) b) (terms 17 b) ∧
    RampFacts (row 17).high (CleanupRows82427.data 17).steps (At (row 17) (length (by decide)) b) (ramps 17 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts17

theorem slope17 : PhaseRampSlope82427.RowSlope (row 17) (length (by decide))
    (terms 17) (ramps 17)=slope 17 := by decide +kernel
#print axioms slope17

theorem facts18 (b : CrossBandCredit208.Band) :
    BandFacts (row 18).high (CleanupRows82427.data 18).steps (At (row 18) (length (by decide)) b) (terms 18 b) ∧
    RampFacts (row 18).high (CleanupRows82427.data 18).steps (At (row 18) (length (by decide)) b) (ramps 18 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts18

theorem slope18 : PhaseRampSlope82427.RowSlope (row 18) (length (by decide))
    (terms 18) (ramps 18)=slope 18 := by decide +kernel
#print axioms slope18

theorem facts19 (b : CrossBandCredit208.Band) :
    BandFacts (row 19).high (CleanupRows82427.data 19).steps (At (row 19) (length (by decide)) b) (terms 19 b) ∧
    RampFacts (row 19).high (CleanupRows82427.data 19).steps (At (row 19) (length (by decide)) b) (ramps 19 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts19

theorem slope19 : PhaseRampSlope82427.RowSlope (row 19) (length (by decide))
    (terms 19) (ramps 19)=slope 19 := by decide +kernel
#print axioms slope19

theorem facts20 (b : CrossBandCredit208.Band) :
    BandFacts (row 20).high (CleanupRows82427.data 20).steps (At (row 20) (length (by decide)) b) (terms 20 b) ∧
    RampFacts (row 20).high (CleanupRows82427.data 20).steps (At (row 20) (length (by decide)) b) (ramps 20 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts20

theorem slope20 : PhaseRampSlope82427.RowSlope (row 20) (length (by decide))
    (terms 20) (ramps 20)=slope 20 := by decide +kernel
#print axioms slope20

theorem facts21 (b : CrossBandCredit208.Band) :
    BandFacts (row 21).high (CleanupRows82427.data 21).steps (At (row 21) (length (by decide)) b) (terms 21 b) ∧
    RampFacts (row 21).high (CleanupRows82427.data 21).steps (At (row 21) (length (by decide)) b) (ramps 21 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts21

theorem slope21 : PhaseRampSlope82427.RowSlope (row 21) (length (by decide))
    (terms 21) (ramps 21)=slope 21 := by decide +kernel
#print axioms slope21

theorem facts22 (b : CrossBandCredit208.Band) :
    BandFacts (row 22).high (CleanupRows82427.data 22).steps (At (row 22) (length (by decide)) b) (terms 22 b) ∧
    RampFacts (row 22).high (CleanupRows82427.data 22).steps (At (row 22) (length (by decide)) b) (ramps 22 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts22

theorem slope22 : PhaseRampSlope82427.RowSlope (row 22) (length (by decide))
    (terms 22) (ramps 22)=slope 22 := by decide +kernel
#print axioms slope22

theorem facts23 (b : CrossBandCredit208.Band) :
    BandFacts (row 23).high (CleanupRows82427.data 23).steps (At (row 23) (length (by decide)) b) (terms 23 b) ∧
    RampFacts (row 23).high (CleanupRows82427.data 23).steps (At (row 23) (length (by decide)) b) (ramps 23 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts23

theorem slope23 : PhaseRampSlope82427.RowSlope (row 23) (length (by decide))
    (terms 23) (ramps 23)=slope 23 := by decide +kernel
#print axioms slope23

theorem facts24 (b : CrossBandCredit208.Band) :
    BandFacts (row 24).high (CleanupRows82427.data 24).steps (At (row 24) (length (by decide)) b) (terms 24 b) ∧
    RampFacts (row 24).high (CleanupRows82427.data 24).steps (At (row 24) (length (by decide)) b) (ramps 24 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts24

theorem slope24 : PhaseRampSlope82427.RowSlope (row 24) (length (by decide))
    (terms 24) (ramps 24)=slope 24 := by decide +kernel
#print axioms slope24

theorem facts25 (b : CrossBandCredit208.Band) :
    BandFacts (row 25).high (CleanupRows82427.data 25).steps (At (row 25) (length (by decide)) b) (terms 25 b) ∧
    RampFacts (row 25).high (CleanupRows82427.data 25).steps (At (row 25) (length (by decide)) b) (ramps 25 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts25

theorem slope25 : PhaseRampSlope82427.RowSlope (row 25) (length (by decide))
    (terms 25) (ramps 25)=slope 25 := by decide +kernel
#print axioms slope25

theorem facts26 (b : CrossBandCredit208.Band) :
    BandFacts (row 26).high (CleanupRows82427.data 26).steps (At (row 26) (length (by decide)) b) (terms 26 b) ∧
    RampFacts (row 26).high (CleanupRows82427.data 26).steps (At (row 26) (length (by decide)) b) (ramps 26 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts26

theorem slope26 : PhaseRampSlope82427.RowSlope (row 26) (length (by decide))
    (terms 26) (ramps 26)=slope 26 := by decide +kernel
#print axioms slope26

theorem facts27 (b : CrossBandCredit208.Band) :
    BandFacts (row 27).high (CleanupRows82427.data 27).steps (At (row 27) (length (by decide)) b) (terms 27 b) ∧
    RampFacts (row 27).high (CleanupRows82427.data 27).steps (At (row 27) (length (by decide)) b) (ramps 27 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts27

theorem slope27 : PhaseRampSlope82427.RowSlope (row 27) (length (by decide))
    (terms 27) (ramps 27)=slope 27 := by decide +kernel
#print axioms slope27

theorem facts28 (b : CrossBandCredit208.Band) :
    BandFacts (row 28).high (CleanupRows82427.data 28).steps (At (row 28) (length (by decide)) b) (terms 28 b) ∧
    RampFacts (row 28).high (CleanupRows82427.data 28).steps (At (row 28) (length (by decide)) b) (ramps 28 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts28

theorem slope28 : PhaseRampSlope82427.RowSlope (row 28) (length (by decide))
    (terms 28) (ramps 28)=slope 28 := by decide +kernel
#print axioms slope28

theorem facts29 (b : CrossBandCredit208.Band) :
    BandFacts (row 29).high (CleanupRows82427.data 29).steps (At (row 29) (length (by decide)) b) (terms 29 b) ∧
    RampFacts (row 29).high (CleanupRows82427.data 29).steps (At (row 29) (length (by decide)) b) (ramps 29 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts29

theorem slope29 : PhaseRampSlope82427.RowSlope (row 29) (length (by decide))
    (terms 29) (ramps 29)=slope 29 := by decide +kernel
#print axioms slope29

theorem facts30 (b : CrossBandCredit208.Band) :
    BandFacts (row 30).high (CleanupRows82427.data 30).steps (At (row 30) (length (by decide)) b) (terms 30 b) ∧
    RampFacts (row 30).high (CleanupRows82427.data 30).steps (At (row 30) (length (by decide)) b) (ramps 30 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts30

theorem slope30 : PhaseRampSlope82427.RowSlope (row 30) (length (by decide))
    (terms 30) (ramps 30)=slope 30 := by decide +kernel
#print axioms slope30

theorem facts31 (b : CrossBandCredit208.Band) :
    BandFacts (row 31).high (CleanupRows82427.data 31).steps (At (row 31) (length (by decide)) b) (terms 31 b) ∧
    RampFacts (row 31).high (CleanupRows82427.data 31).steps (At (row 31) (length (by decide)) b) (ramps 31 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts31

theorem slope31 : PhaseRampSlope82427.RowSlope (row 31) (length (by decide))
    (terms 31) (ramps 31)=slope 31 := by decide +kernel
#print axioms slope31

end
end JSP233.RowLightChecks82427G01
