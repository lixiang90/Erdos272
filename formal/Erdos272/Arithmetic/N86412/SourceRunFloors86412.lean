module

public import Erdos272.Counting.N86412.RunPlans86412
public import Erdos272.Arithmetic.N86412.SourceFloors86412

@[expose] public section

namespace JSP233.SourceRunFloors86412
open RunPlans86412 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hi : i < 21) :
    Floor (plan i).upper (plan i).defect (plan i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors86412.floor000
  · exact weaken (by decide) (by decide) SourceFloors86412.floor001
  · exact weaken (by decide) (by decide) SourceFloors86412.floor002
  · exact weaken (by decide) (by decide) SourceFloors86412.floor003
  · exact weaken (by decide) (by decide) SourceFloors86412.floor004
  · exact weaken (by decide) (by decide) SourceFloors86412.floor005
  · exact weaken (by decide) (by decide) SourceFloors86412.floor006
  · exact weaken (by decide) (by decide) SourceFloors86412.floor007
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors118533.floor027
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors88404.floor094
  · exact weaken (by decide) (by decide) SourceFloors86412.floor008
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors88404.floor098
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors88404.floor098
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors88404.floor098
  · exact weaken (by decide) (by decide) SourceFloors86412.floor009
  · exact weaken (by decide) (by decide) SourceFloors86412.floor010
  · exact weaken (by decide) (by decide) SourceFloors86412.floor011
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors88404.floor112
  · exact weaken (by decide) (by decide) SourceFloors86412.floor012
  · exact weaken (by decide) (by decide) SourceFloors86412.floor013
  · exact weaken (by decide) (by decide) SourceFloors86412.floor021

#print axioms floors
end JSP233.SourceRunFloors86412
