module

public import Erdos272.Arithmetic.N158375.SourceQueryData158375
public import Erdos272.Arithmetic.N158375.SourceFloors158375

@[expose] public section

namespace JSP233.SourceQueryFloors158375G2
open SourceQueryData158375 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hlo : 107 ≤ i) (hhi : i < 143) :
    Floor (query i).lower (query i).cutoff (query i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors158375.floor019
  · exact weaken (by decide) (by decide) SourceFloors158375.floor079
  · exact weaken (by decide) (by decide) SourceFloors158375.floor065
  · exact weaken (by decide) (by decide) SourceFloors158375.floor046
  · exact weaken (by decide) (by decide) SourceFloors158375.floor038
  · exact weaken (by decide) (by decide) SourceFloors158375.floor031
  · exact weaken (by decide) (by decide) SourceFloors158375.floor014
  · exact weaken (by decide) (by decide) SourceFloors158375.floor003
  · exact weaken (by decide) (by decide) SourceFloors158375.floor106
  · exact weaken (by decide) (by decide) SourceFloors158375.floor090
  · exact weaken (by decide) (by decide) SourceFloors158375.floor074
  · exact weaken (by decide) (by decide) SourceFloors158375.floor056
  · exact weaken (by decide) (by decide) SourceFloors158375.floor043
  · exact weaken (by decide) (by decide) SourceFloors158375.floor029
  · exact weaken (by decide) (by decide) SourceFloors158375.floor008
  · exact weaken (by decide) (by decide) SourceFloors158375.floor118
  · exact weaken (by decide) (by decide) SourceFloors158375.floor103
  · exact weaken (by decide) (by decide) SourceFloors158375.floor089
  · exact weaken (by decide) (by decide) SourceFloors158375.floor073
  · exact weaken (by decide) (by decide) SourceFloors158375.floor051
  · exact weaken (by decide) (by decide) SourceFloors158375.floor034
  · exact weaken (by decide) (by decide) SourceFloors158375.floor016
  · exact weaken (by decide) (by decide) SourceFloors158375.floor122
  · exact weaken (by decide) (by decide) SourceFloors158375.floor110
  · exact weaken (by decide) (by decide) SourceFloors158375.floor094
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors291012.floor282
  · exact weaken (by decide) (by decide) SourceFloors158375.floor061
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors190000.floor044
  · exact weaken (by decide) (by decide) SourceFloors158375.floor022
  · exact weaken (by decide) (by decide) SourceFloors158375.floor126
  · exact weaken (by decide) (by decide) SourceFloors158375.floor114
  · exact weaken (by decide) (by decide) SourceFloors158375.floor101
  · exact weaken (by decide) (by decide) SourceFloors158375.floor086
  · exact weaken (by decide) (by decide) SourceFloors158375.floor068
  · exact weaken (by decide) (by decide) SourceFloors158375.floor059
  · exact weaken (by decide) (by decide) SourceFloors158375.floor022

#print axioms floors
end JSP233.SourceQueryFloors158375G2
