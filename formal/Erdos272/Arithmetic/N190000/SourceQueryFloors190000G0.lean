module

public import Erdos272.Arithmetic.N190000.SourceQueryData190000
public import Erdos272.Arithmetic.N190000.SourceFloors190000

@[expose] public section

namespace JSP233.SourceQueryFloors190000G0
open SourceQueryData190000 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hlo : 0 ≤ i) (hhi : i < 50) :
    Floor (query i).lower (query i).cutoff (query i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors190000.floor007
  · exact weaken (by decide) (by decide) SourceFloors190000.floor054
  · exact weaken (by decide) (by decide) SourceFloors190000.floor041
  · exact weaken (by decide) (by decide) SourceFloors190000.floor032
  · exact weaken (by decide) (by decide) SourceFloors190000.floor022
  · exact weaken (by decide) (by decide) SourceFloors190000.floor016
  · exact weaken (by decide) (by decide) SourceFloors190000.floor009
  · exact weaken (by decide) (by decide) SourceFloors190000.floor000
  · exact weaken (by decide) (by decide) SourceFloors190000.floor072
  · exact weaken (by decide) (by decide) SourceFloors190000.floor060
  · exact weaken (by decide) (by decide) SourceFloors190000.floor048
  · exact weaken (by decide) (by decide) SourceFloors190000.floor038
  · exact weaken (by decide) (by decide) SourceFloors190000.floor025
  · exact weaken (by decide) (by decide) SourceFloors190000.floor018
  · exact weaken (by decide) (by decide) SourceFloors190000.floor002
  · exact weaken (by decide) (by decide) SourceFloors190000.floor084
  · exact weaken (by decide) (by decide) SourceFloors190000.floor073
  · exact weaken (by decide) (by decide) SourceFloors190000.floor061
  · exact weaken (by decide) (by decide) SourceFloors190000.floor049
  · exact weaken (by decide) (by decide) SourceFloors190000.floor036
  · exact weaken (by decide) (by decide) SourceFloors190000.floor020
  · exact weaken (by decide) (by decide) SourceFloors190000.floor005
  · exact weaken (by decide) (by decide) SourceFloors190000.floor090
  · exact weaken (by decide) (by decide) SourceFloors190000.floor080
  · exact weaken (by decide) (by decide) SourceFloors190000.floor068
  · exact weaken (by decide) (by decide) SourceFloors190000.floor056
  · exact weaken (by decide) (by decide) SourceFloors190000.floor040
  · exact weaken (by decide) (by decide) SourceFloors190000.floor024
  · exact weaken (by decide) (by decide) SourceFloors190000.floor010
  · exact weaken (by decide) (by decide) SourceFloors190000.floor092
  · exact weaken (by decide) (by decide) SourceFloors190000.floor082
  · exact weaken (by decide) (by decide) SourceFloors190000.floor070
  · exact weaken (by decide) (by decide) SourceFloors190000.floor058
  · exact weaken (by decide) (by decide) SourceFloors190000.floor044
  · exact weaken (by decide) (by decide) SourceFloors190000.floor028
  · exact weaken (by decide) (by decide) SourceFloors190000.floor012
  · exact weaken (by decide) (by decide) SourceFloors190000.floor094
  · exact weaken (by decide) (by decide) SourceFloors190000.floor086
  · exact weaken (by decide) (by decide) SourceFloors190000.floor076
  · exact weaken (by decide) (by decide) SourceFloors190000.floor064
  · exact weaken (by decide) (by decide) SourceFloors190000.floor046
  · exact weaken (by decide) (by decide) SourceFloors190000.floor030
  · exact weaken (by decide) (by decide) SourceFloors190000.floor012
  · exact weaken (by decide) (by decide) SourceFloors190000.floor096
  · exact weaken (by decide) (by decide) SourceFloors190000.floor088
  · exact weaken (by decide) (by decide) SourceFloors190000.floor078
  · exact weaken (by decide) (by decide) SourceFloors190000.floor066
  · exact weaken (by decide) (by decide) SourceFloors190000.floor051
  · exact weaken (by decide) (by decide) SourceFloors190000.floor034
  · exact weaken (by decide) (by decide) SourceFloors190000.floor014

#print axioms floors
end JSP233.SourceQueryFloors190000G0
