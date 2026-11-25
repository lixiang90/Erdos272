module

public import Erdos272.Arithmetic.N158375.UnitFloorChecks158375G0
public import Erdos272.Arithmetic.N158375.UnitFloorChecks158375G1
public import Erdos272.Arithmetic.N158375.UnitFloorChecks158375G2
public import Erdos272.Arithmetic.N158375.UnitFloorChecks158375G3

@[expose] public section

namespace JSP233.UnitFloor158375
open CoreUnionSource200000 UnitFloorData158375
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem unitFloor_mono : Monotone unitFloor := by
  apply monotone_nat_of_le_succ
  intro a
  by_cases ha : a < 768
  · exact of_decide_eq_true (List.all_eq_true.mp adjacent_checked a (List.mem_range.mpr ha))
  · simp only [unitFloor, if_neg ha, if_neg (show ¬a+1 < 768 by omega), le_refl]

theorem unitFloor_le_tail (a : ℕ) : unitFloor a ≤ 155000 := by
  by_cases ha : a < 768
  · exact of_decide_eq_true (List.all_eq_true.mp maximum_checked a (List.mem_range.mpr ha))
  · simp only [unitFloor, if_neg ha, le_refl]

theorem unitFloor_bound {a : ℕ} (ha : a ≤ 2^18) : unitFloor a ≤ UnitBound a := by
  by_cases h₀ : a < 192
  · exact UnitFloorChecks158375G0.bound (by omega) h₀
  by_cases h₁ : a < 384
  · exact UnitFloorChecks158375G1.bound (by omega) h₁
  by_cases h₂ : a < 576
  · exact UnitFloorChecks158375G2.bound (by omega) h₂
  by_cases h₃ : a < 768
  · exact UnitFloorChecks158375G3.bound (by omega) h₃
  · exact (unitFloor_le_tail a).trans
      (AnalyticCore180000.floor_large (t := 768) (by omega) ha (by decide) (by decide))

theorem uniform_unit_floor {a t : ℕ} (ht : t ≤ a) (ha : a ≤ 2^18) :
    unitFloor t ≤ UnitBound a := (unitFloor_mono ht).trans (unitFloor_bound ha)

#print axioms unitFloor_mono
#print axioms unitFloor_le_tail
#print axioms unitFloor_bound
#print axioms uniform_unit_floor
end JSP233.UnitFloor158375
