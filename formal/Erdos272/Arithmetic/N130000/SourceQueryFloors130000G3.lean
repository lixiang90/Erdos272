module

public import Erdos272.Arithmetic.N130000.SourceQueryData130000
public import Erdos272.Arithmetic.N130000.SourceFloors130000

@[expose] public section

namespace JSP233.SourceQueryFloors130000G3
open SourceQueryData130000 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hlo : 311 ≤ i) (hhi : i < 340) :
    Floor (query i).lower (query i).cutoff (query i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors130000.floor025
  · exact weaken (by decide) (by decide) SourceFloors130000.floor102
  · exact weaken (by decide) (by decide) SourceFloors130000.floor086
  · exact weaken (by decide) (by decide) SourceFloors130000.floor045
  · exact weaken (by decide) (by decide) SourceFloors130000.floor026
  · exact weaken (by decide) (by decide) SourceFloors130000.floor005
  · exact weaken (by decide) (by decide) SourceFloors130000.floor005
  · exact weaken (by decide) (by decide) SourceFloors130000.floor005
  · exact weaken (by decide) (by decide) SourceFloors130000.floor135
  · exact weaken (by decide) (by decide) SourceFloors130000.floor115
  · exact weaken (by decide) (by decide) SourceFloors130000.floor085
  · exact weaken (by decide) (by decide) SourceFloors130000.floor070
  · exact weaken (by decide) (by decide) SourceFloors130000.floor010
  · exact weaken (by decide) (by decide) SourceFloors130000.floor010
  · exact weaken (by decide) (by decide) SourceFloors130000.floor010
  · exact weaken (by decide) (by decide) SourceFloors130000.floor145
  · exact weaken (by decide) (by decide) SourceFloors130000.floor122
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors142758.floor114
  · exact weaken (by decide) (by decide) SourceFloors130000.floor078
  · exact weaken (by decide) (by decide) SourceFloors130000.floor017
  · exact weaken (by decide) (by decide) SourceFloors130000.floor017
  · exact weaken (by decide) (by decide) SourceFloors130000.floor017
  · exact weaken (by decide) (by decide) SourceFloors130000.floor156
  · exact weaken (by decide) (by decide) SourceFloors130000.floor129
  · exact weaken (by decide) (by decide) SourceFloors130000.floor098
  · exact weaken (by decide) (by decide) SourceFloors130000.floor082
  · exact weaken (by decide) (by decide) SourceFloors130000.floor023
  · exact weaken (by decide) (by decide) SourceFloors130000.floor023
  · exact weaken (by decide) (by decide) SourceFloors130000.floor023

#print axioms floors
end JSP233.SourceQueryFloors130000G3
