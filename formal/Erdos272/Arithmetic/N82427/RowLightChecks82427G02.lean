module

public import Erdos272.Arithmetic.N82427.RowLightData82427

@[expose] public section

namespace JSP233.RowLightChecks82427G02
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

theorem facts32 (b : CrossBandCredit208.Band) :
    BandFacts (row 32).high (CleanupRows82427.data 32).steps (At (row 32) (length (by decide)) b) (terms 32 b) ∧
    RampFacts (row 32).high (CleanupRows82427.data 32).steps (At (row 32) (length (by decide)) b) (ramps 32 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts32

theorem slope32 : PhaseRampSlope82427.RowSlope (row 32) (length (by decide))
    (terms 32) (ramps 32)=slope 32 := by decide +kernel
#print axioms slope32

theorem facts33 (b : CrossBandCredit208.Band) :
    BandFacts (row 33).high (CleanupRows82427.data 33).steps (At (row 33) (length (by decide)) b) (terms 33 b) ∧
    RampFacts (row 33).high (CleanupRows82427.data 33).steps (At (row 33) (length (by decide)) b) (ramps 33 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts33

theorem slope33 : PhaseRampSlope82427.RowSlope (row 33) (length (by decide))
    (terms 33) (ramps 33)=slope 33 := by decide +kernel
#print axioms slope33

theorem facts34 (b : CrossBandCredit208.Band) :
    BandFacts (row 34).high (CleanupRows82427.data 34).steps (At (row 34) (length (by decide)) b) (terms 34 b) ∧
    RampFacts (row 34).high (CleanupRows82427.data 34).steps (At (row 34) (length (by decide)) b) (ramps 34 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts34

theorem slope34 : PhaseRampSlope82427.RowSlope (row 34) (length (by decide))
    (terms 34) (ramps 34)=slope 34 := by decide +kernel
#print axioms slope34

theorem facts35 (b : CrossBandCredit208.Band) :
    BandFacts (row 35).high (CleanupRows82427.data 35).steps (At (row 35) (length (by decide)) b) (terms 35 b) ∧
    RampFacts (row 35).high (CleanupRows82427.data 35).steps (At (row 35) (length (by decide)) b) (ramps 35 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts35

theorem slope35 : PhaseRampSlope82427.RowSlope (row 35) (length (by decide))
    (terms 35) (ramps 35)=slope 35 := by decide +kernel
#print axioms slope35

theorem facts36 (b : CrossBandCredit208.Band) :
    BandFacts (row 36).high (CleanupRows82427.data 36).steps (At (row 36) (length (by decide)) b) (terms 36 b) ∧
    RampFacts (row 36).high (CleanupRows82427.data 36).steps (At (row 36) (length (by decide)) b) (ramps 36 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts36

theorem slope36 : PhaseRampSlope82427.RowSlope (row 36) (length (by decide))
    (terms 36) (ramps 36)=slope 36 := by decide +kernel
#print axioms slope36

theorem facts37 (b : CrossBandCredit208.Band) :
    BandFacts (row 37).high (CleanupRows82427.data 37).steps (At (row 37) (length (by decide)) b) (terms 37 b) ∧
    RampFacts (row 37).high (CleanupRows82427.data 37).steps (At (row 37) (length (by decide)) b) (ramps 37 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts37

theorem slope37 : PhaseRampSlope82427.RowSlope (row 37) (length (by decide))
    (terms 37) (ramps 37)=slope 37 := by decide +kernel
#print axioms slope37

theorem facts38 (b : CrossBandCredit208.Band) :
    BandFacts (row 38).high (CleanupRows82427.data 38).steps (At (row 38) (length (by decide)) b) (terms 38 b) ∧
    RampFacts (row 38).high (CleanupRows82427.data 38).steps (At (row 38) (length (by decide)) b) (ramps 38 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts38

theorem slope38 : PhaseRampSlope82427.RowSlope (row 38) (length (by decide))
    (terms 38) (ramps 38)=slope 38 := by decide +kernel
#print axioms slope38

theorem facts39 (b : CrossBandCredit208.Band) :
    BandFacts (row 39).high (CleanupRows82427.data 39).steps (At (row 39) (length (by decide)) b) (terms 39 b) ∧
    RampFacts (row 39).high (CleanupRows82427.data 39).steps (At (row 39) (length (by decide)) b) (ramps 39 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts39

theorem slope39 : PhaseRampSlope82427.RowSlope (row 39) (length (by decide))
    (terms 39) (ramps 39)=slope 39 := by decide +kernel
#print axioms slope39

theorem facts40 (b : CrossBandCredit208.Band) :
    BandFacts (row 40).high (CleanupRows82427.data 40).steps (At (row 40) (length (by decide)) b) (terms 40 b) ∧
    RampFacts (row 40).high (CleanupRows82427.data 40).steps (At (row 40) (length (by decide)) b) (ramps 40 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts40

theorem slope40 : PhaseRampSlope82427.RowSlope (row 40) (length (by decide))
    (terms 40) (ramps 40)=slope 40 := by decide +kernel
#print axioms slope40

theorem facts41 (b : CrossBandCredit208.Band) :
    BandFacts (row 41).high (CleanupRows82427.data 41).steps (At (row 41) (length (by decide)) b) (terms 41 b) ∧
    RampFacts (row 41).high (CleanupRows82427.data 41).steps (At (row 41) (length (by decide)) b) (ramps 41 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts41

theorem slope41 : PhaseRampSlope82427.RowSlope (row 41) (length (by decide))
    (terms 41) (ramps 41)=slope 41 := by decide +kernel
#print axioms slope41

theorem facts42 (b : CrossBandCredit208.Band) :
    BandFacts (row 42).high (CleanupRows82427.data 42).steps (At (row 42) (length (by decide)) b) (terms 42 b) ∧
    RampFacts (row 42).high (CleanupRows82427.data 42).steps (At (row 42) (length (by decide)) b) (ramps 42 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts42

theorem slope42 : PhaseRampSlope82427.RowSlope (row 42) (length (by decide))
    (terms 42) (ramps 42)=slope 42 := by decide +kernel
#print axioms slope42

theorem facts43 (b : CrossBandCredit208.Band) :
    BandFacts (row 43).high (CleanupRows82427.data 43).steps (At (row 43) (length (by decide)) b) (terms 43 b) ∧
    RampFacts (row 43).high (CleanupRows82427.data 43).steps (At (row 43) (length (by decide)) b) (ramps 43 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts43

theorem slope43 : PhaseRampSlope82427.RowSlope (row 43) (length (by decide))
    (terms 43) (ramps 43)=slope 43 := by decide +kernel
#print axioms slope43

theorem facts44 (b : CrossBandCredit208.Band) :
    BandFacts (row 44).high (CleanupRows82427.data 44).steps (At (row 44) (length (by decide)) b) (terms 44 b) ∧
    RampFacts (row 44).high (CleanupRows82427.data 44).steps (At (row 44) (length (by decide)) b) (ramps 44 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts44

theorem slope44 : PhaseRampSlope82427.RowSlope (row 44) (length (by decide))
    (terms 44) (ramps 44)=slope 44 := by decide +kernel
#print axioms slope44

theorem facts45 (b : CrossBandCredit208.Band) :
    BandFacts (row 45).high (CleanupRows82427.data 45).steps (At (row 45) (length (by decide)) b) (terms 45 b) ∧
    RampFacts (row 45).high (CleanupRows82427.data 45).steps (At (row 45) (length (by decide)) b) (ramps 45 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts45

theorem slope45 : PhaseRampSlope82427.RowSlope (row 45) (length (by decide))
    (terms 45) (ramps 45)=slope 45 := by decide +kernel
#print axioms slope45

theorem facts46 (b : CrossBandCredit208.Band) :
    BandFacts (row 46).high (CleanupRows82427.data 46).steps (At (row 46) (length (by decide)) b) (terms 46 b) ∧
    RampFacts (row 46).high (CleanupRows82427.data 46).steps (At (row 46) (length (by decide)) b) (ramps 46 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts46

theorem slope46 : PhaseRampSlope82427.RowSlope (row 46) (length (by decide))
    (terms 46) (ramps 46)=slope 46 := by decide +kernel
#print axioms slope46

theorem facts47 (b : CrossBandCredit208.Band) :
    BandFacts (row 47).high (CleanupRows82427.data 47).steps (At (row 47) (length (by decide)) b) (terms 47 b) ∧
    RampFacts (row 47).high (CleanupRows82427.data 47).steps (At (row 47) (length (by decide)) b) (ramps 47 b) := by
  fin_cases b <;> decide +kernel
#print axioms facts47

theorem slope47 : PhaseRampSlope82427.RowSlope (row 47) (length (by decide))
    (terms 47) (ramps 47)=slope 47 := by decide +kernel
#print axioms slope47

end
end JSP233.RowLightChecks82427G02
