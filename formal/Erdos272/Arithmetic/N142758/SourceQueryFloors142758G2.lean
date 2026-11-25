module

public import Erdos272.Arithmetic.N142758.SourceQueryData142758
public import Erdos272.Arithmetic.N142758.SourceFloors142758

@[expose] public section

namespace JSP233.SourceQueryFloors142758G2
open SourceQueryData142758 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hlo : 240 ≤ i) (hhi : i < 269) :
    Floor (query i).lower (query i).cutoff (query i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors142758.floor030
  · exact weaken (by decide) (by decide) SourceFloors142758.floor125
  · exact weaken (by decide) (by decide) SourceFloors142758.floor103
  · exact weaken (by decide) (by decide) SourceFloors142758.floor073
  · exact weaken (by decide) (by decide) SourceFloors142758.floor058
  · exact weaken (by decide) (by decide) SourceFloors142758.floor049
  · exact weaken (by decide) (by decide) SourceFloors142758.floor031
  · exact weaken (by decide) (by decide) SourceFloors142758.floor008
  · exact weaken (by decide) (by decide) SourceFloors142758.floor168
  · exact weaken (by decide) (by decide) SourceFloors142758.floor145
  · exact weaken (by decide) (by decide) SourceFloors142758.floor122
  · exact weaken (by decide) (by decide) SourceFloors142758.floor099
  · exact weaken (by decide) (by decide) SourceFloors142758.floor077
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors151879.floor016
  · exact weaken (by decide) (by decide) SourceFloors142758.floor017
  · exact weaken (by decide) (by decide) SourceFloors142758.floor184
  · exact weaken (by decide) (by decide) SourceFloors142758.floor161
  · exact weaken (by decide) (by decide) SourceFloors142758.floor138
  · exact weaken (by decide) (by decide) SourceFloors142758.floor114
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors153080.floor027
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors190000.floor024
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors151879.floor008
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors190000.floor092
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors190000.floor082
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors190000.floor070
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors190000.floor058
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors190000.floor044
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors190000.floor044
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors153080.floor010

#print axioms floors
end JSP233.SourceQueryFloors142758G2
