module

public import Erdos272.Arithmetic.N291012.CleanupRows291012
public import Erdos272.Resources.ActualUnitRecipe208
public import Erdos272.Resources.N291012.ActualUnitCut291012

@[expose] public section

namespace JSP233.RowStatic291012
open StarCompletion CleanupRows291012 UnitRecipeStatic208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

structure Static (v : Data) : Prop where
  length : v.row.bands.length = 7
  member_two : 2 ≤ v.memberFloor
  defect_two : 2 ≤ v.row.i
  defect_lt : v.row.i < v.memberFloor
  low_pos : 0 < v.row.low
  low_high : v.row.low ≤ v.row.high
  high_bound : v.row.high < 2^50
  grid : v.row.grid = 1000000000000
  steps : v.steps = v.row.high/(v.memberFloor-v.row.i)
  first : (evalData v.row 0).T = v.memberFloor
  last : (evalData v.row 6).U = v.row.high/12+1
  joins : ∀ b : Fin 6, (evalData v.row b.castSucc).U = (evalData v.row b.succ).T
  bands : ∀ b : Fin 7, v.memberFloor ≤ (evalData v.row b).T ∧
    (evalData v.row b).E ≤ v.row.i ∧ (evalData v.row b).T < (evalData v.row b).U

end
end JSP233.RowStatic291012
