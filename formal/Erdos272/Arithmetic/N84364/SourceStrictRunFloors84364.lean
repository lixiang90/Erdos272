module

public import Erdos272.Counting.N84364.StrictRunPlans84364
public import Erdos272.Arithmetic.N84364.SourceFloors84364

@[expose] public section

namespace JSP233.SourceStrictRunFloors84364
open StrictRunPlans84364 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hi : i < 24) :
    Floor (plan i).upper (plan i).defect (plan i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors84364.floor000
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors86412.floor002
  · exact weaken (by decide) (by decide) SourceFloors84364.floor001
  · exact weaken (by decide) (by decide) SourceFloors84364.floor002
  · exact weaken (by decide) (by decide) SourceFloors84364.floor003
  · exact weaken (by decide) (by decide) SourceFloors84364.floor004
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors118533.floor027
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors86412.floor008
  · exact weaken (by decide) (by decide) SourceFloors84364.floor005
  · exact weaken (by decide) (by decide) SourceFloors84364.floor005
  · exact weaken (by decide) (by decide) SourceFloors84364.floor006
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors86412.floor011
  · exact weaken (by decide) (by decide) SourceFloors84364.floor007
  · exact weaken (by decide) (by decide) SourceFloors84364.floor008
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors86412.floor015
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors88404.floor132
  · exact weaken (by decide) (by decide) SourceFloors84364.floor009
  · exact weaken (by decide) (by decide) SourceFloors84364.floor010
  · exact weaken (by decide) (by decide) SourceFloors84364.floor011
  · exact weaken (by decide) (by decide) SourceFloors84364.floor012
  · exact weaken (by decide) (by decide) SourceFloors84364.floor013
  · exact weaken (by decide) (by decide) SourceFloors84364.floor014
  · exact weaken (by decide) (by decide) SourceFloors84364.floor015
  · exact weaken (by decide) (by decide) SourceFloors84364.floor016

#print axioms floors
end JSP233.SourceStrictRunFloors84364
