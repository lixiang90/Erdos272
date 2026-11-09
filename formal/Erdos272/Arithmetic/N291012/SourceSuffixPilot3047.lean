module

public import Erdos272.Arithmetic.N291012.SourceFloors291012
public import Erdos272.Resources.N291012.LowResourceBridges3040

@[expose] public section

namespace JSP233.SourceSuffixPilot3047
open SourceFloorSound291012 PureSource208
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

-- One required 251008-window floor, extended from the certified suffix at 5760.

def strides0 : List ℕ :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2,
   2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2]

theorem checked0 : CoverCheck 4896 5177 9 119312 strides0 = true := by
  decide +kernel

theorem bound0 : ∀ s, 4896 ≤ s → s < 5177 → 119312 ≤ physicalK s 9 :=
  cover_sound strides0 4896 (by decide) checked0

def strides1 : List ℕ :=
  [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2,
   1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2,
   1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1,
   1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2,
   1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2,
   1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1,
   1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2,
   1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2,
   1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2,
   2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2,
   2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2]

theorem checked1 : CoverCheck 5177 5555 9 119312 strides1 = true := by
  decide +kernel

theorem bound1 : ∀ s, 5177 ≤ s → s < 5555 → 119312 ≤ physicalK s 9 :=
  cover_sound strides1 5177 (by decide) checked1

def strides2 : List ℕ :=
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
   2, 2, 2, 2, 2, 2, 2, 1]

theorem checked2 : CoverCheck 5555 5760 9 119312 strides2 = true := by
  decide +kernel

theorem bound2 : ∀ s, 5555 ≤ s → s < 5760 → 119312 ≤ physicalK s 9 :=
  cover_sound strides2 5555 (by decide) checked2

theorem prefix_bound : ∀ s, 4896 ≤ s → s < 5760 → 119312 ≤ physicalK s 9 :=
  append_cover bound0 (append_cover bound1 bound2)

theorem extended_floor : Floor 4896 9 119312 := by
  have hsuffix : Floor 5760 9 119312 :=
    LowResourceBridges3040.floor_weaken_defect le_rfl (by decide) (by decide)
      SourceFloors291012.floor014
  intro s hs hbig
  by_cases h : s < 5760
  · exact prefix_bound s hs h
  · exact hsuffix s (by omega) hbig

#print axioms checked0
#print axioms bound0
#print axioms checked1
#print axioms bound1
#print axioms checked2
#print axioms bound2
#print axioms prefix_bound
#print axioms extended_floor
end JSP233.SourceSuffixPilot3047
