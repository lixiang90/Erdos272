module

public import Erdos272.Counting.N118533.RunPlans118533
public import Erdos272.Arithmetic.N118533.SourceFloors118533

@[expose] public section

namespace JSP233.SourceRunFloors118533
open RunPlans118533 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hi : i < 13) :
    Floor (plan i).upper (plan i).defect (plan i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors118533.floor040
  · exact weaken (by decide) (by decide) SourceFloors118533.floor045
  · exact weaken (by decide) (by decide) SourceFloors118533.floor048
  · exact weaken (by decide) (by decide) SourceFloors118533.floor052
  · exact weaken (by decide) (by decide) SourceFloors118533.floor055
  · exact weaken (by decide) (by decide) SourceFloors118533.floor057
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors142758.floor187
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors142758.floor190
  · exact weaken (by decide) (by decide) SourceFloors118533.floor047
  · exact weaken (by decide) (by decide) SourceFloors118533.floor054
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors155716.floor051
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors153080.floor055
  · exact weaken (by decide) (by decide) SourceFloors118533.floor056

#print axioms floors
end JSP233.SourceRunFloors118533
