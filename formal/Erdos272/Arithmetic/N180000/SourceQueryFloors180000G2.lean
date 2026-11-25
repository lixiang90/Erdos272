module

public import Erdos272.Arithmetic.N180000.SourceQueryData180000
public import Erdos272.Arithmetic.N180000.SourceFloors180000

@[expose] public section

namespace JSP233.SourceQueryFloors180000G2
open SourceQueryData180000 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hlo : 100 ≤ i) (hhi : i < 150) :
    Floor (query i).lower (query i).cutoff (query i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors180000.floor011
  · exact weaken (by decide) (by decide) SourceFloors180000.floor066
  · exact weaken (by decide) (by decide) SourceFloors180000.floor055
  · exact weaken (by decide) (by decide) SourceFloors180000.floor044
  · exact weaken (by decide) (by decide) SourceFloors180000.floor032
  · exact weaken (by decide) (by decide) SourceFloors180000.floor025
  · exact weaken (by decide) (by decide) SourceFloors180000.floor014
  · exact weaken (by decide) (by decide) SourceFloors180000.floor002
  · exact weaken (by decide) (by decide) SourceFloors180000.floor084
  · exact weaken (by decide) (by decide) SourceFloors180000.floor072
  · exact weaken (by decide) (by decide) SourceFloors180000.floor059
  · exact weaken (by decide) (by decide) SourceFloors180000.floor046
  · exact weaken (by decide) (by decide) SourceFloors180000.floor034
  · exact weaken (by decide) (by decide) SourceFloors180000.floor024
  · exact weaken (by decide) (by decide) SourceFloors180000.floor004
  · exact weaken (by decide) (by decide) SourceFloors180000.floor094
  · exact weaken (by decide) (by decide) SourceFloors180000.floor080
  · exact weaken (by decide) (by decide) SourceFloors180000.floor068
  · exact weaken (by decide) (by decide) SourceFloors180000.floor054
  · exact weaken (by decide) (by decide) SourceFloors180000.floor039
  · exact weaken (by decide) (by decide) SourceFloors180000.floor027
  · exact weaken (by decide) (by decide) SourceFloors180000.floor006
  · exact weaken (by decide) (by decide) SourceFloors180000.floor100
  · exact weaken (by decide) (by decide) SourceFloors180000.floor090
  · exact weaken (by decide) (by decide) SourceFloors180000.floor076
  · exact weaken (by decide) (by decide) SourceFloors180000.floor063
  · exact weaken (by decide) (by decide) SourceFloors180000.floor048
  · exact weaken (by decide) (by decide) SourceFloors180000.floor029
  · exact weaken (by decide) (by decide) SourceFloors180000.floor008
  · exact weaken (by decide) (by decide) SourceFloors180000.floor105
  · exact weaken (by decide) (by decide) SourceFloors180000.floor096
  · exact weaken (by decide) (by decide) SourceFloors180000.floor082
  · exact weaken (by decide) (by decide) SourceFloors180000.floor070
  · exact weaken (by decide) (by decide) SourceFloors180000.floor050
  · exact weaken (by decide) (by decide) SourceFloors180000.floor036
  · exact weaken (by decide) (by decide) SourceFloors180000.floor016
  · exact weaken (by decide) (by decide) SourceFloors180000.floor107
  · exact weaken (by decide) (by decide) SourceFloors180000.floor098
  · exact weaken (by decide) (by decide) SourceFloors180000.floor087
  · exact weaken (by decide) (by decide) SourceFloors180000.floor074
  · exact weaken (by decide) (by decide) SourceFloors180000.floor057
  · exact weaken (by decide) (by decide) SourceFloors180000.floor038
  · exact weaken (by decide) (by decide) SourceFloors180000.floor018
  · exact weaken (by decide) (by decide) SourceFloors180000.floor109
  · exact weaken (by decide) (by decide) SourceFloors180000.floor103
  · exact weaken (by decide) (by decide) SourceFloors180000.floor092
  · exact weaken (by decide) (by decide) SourceFloors180000.floor078
  · exact weaken (by decide) (by decide) SourceFloors180000.floor061
  · exact weaken (by decide) (by decide) SourceFloors180000.floor041
  · exact weaken (by decide) (by decide) SourceFloors180000.floor020

#print axioms floors
end JSP233.SourceQueryFloors180000G2
