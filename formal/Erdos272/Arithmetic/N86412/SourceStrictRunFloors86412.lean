module

public import Erdos272.Counting.N86412.StrictRunPlans86412
public import Erdos272.Arithmetic.N86412.SourceFloors86412

@[expose] public section

namespace JSP233.SourceStrictRunFloors86412
open StrictRunPlans86412 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hi : i < 16) :
    Floor (plan i).upper (plan i).defect (plan i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors86412.floor014
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors88404.floor123
  · exact weaken (by decide) (by decide) SourceFloors86412.floor015
  · exact weaken (by decide) (by decide) SourceFloors86412.floor016
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors88404.floor132
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors88404.floor133
  · exact weaken (by decide) (by decide) SourceFloors86412.floor017
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors88404.floor137
  · exact weaken (by decide) (by decide) SourceFloors86412.floor018
  · exact weaken (by decide) (by decide) SourceFloors86412.floor019
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors88404.floor141
  · exact weaken (by decide) (by decide) SourceFloors86412.floor020
  · exact weaken (by decide) (by decide) SourceFloors86412.floor022
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors88404.floor146
  · exact weaken (by decide) (by decide) SourceFloors86412.floor023
  · exact weaken (by decide) (by decide) SourceFloors86412.floor024

#print axioms floors
end JSP233.SourceStrictRunFloors86412
