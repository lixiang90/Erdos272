module

public import Erdos272.Arithmetic.N200000.SourceQueryData200000
public import Erdos272.Arithmetic.N200000.SourceFloors200000

@[expose] public section

namespace JSP233.SourceQueryFloors200000G2
open SourceQueryData200000 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hlo : 100 ≤ i) (hhi : i < 150) :
    Floor (query i).lower (query i).cutoff (query i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors200000.floor013
  · exact weaken (by decide) (by decide) SourceFloors200000.floor079
  · exact weaken (by decide) (by decide) SourceFloors200000.floor063
  · exact weaken (by decide) (by decide) SourceFloors200000.floor047
  · exact weaken (by decide) (by decide) SourceFloors200000.floor035
  · exact weaken (by decide) (by decide) SourceFloors200000.floor026
  · exact weaken (by decide) (by decide) SourceFloors200000.floor008
  · exact weaken (by decide) (by decide) SourceFloors200000.floor002
  · exact weaken (by decide) (by decide) SourceFloors200000.floor105
  · exact weaken (by decide) (by decide) SourceFloors200000.floor089
  · exact weaken (by decide) (by decide) SourceFloors200000.floor072
  · exact weaken (by decide) (by decide) SourceFloors200000.floor057
  · exact weaken (by decide) (by decide) SourceFloors200000.floor041
  · exact weaken (by decide) (by decide) SourceFloors200000.floor029
  · exact weaken (by decide) (by decide) SourceFloors200000.floor005
  · exact weaken (by decide) (by decide) SourceFloors200000.floor125
  · exact weaken (by decide) (by decide) SourceFloors200000.floor110
  · exact weaken (by decide) (by decide) SourceFloors200000.floor092
  · exact weaken (by decide) (by decide) SourceFloors200000.floor074
  · exact weaken (by decide) (by decide) SourceFloors200000.floor056
  · exact weaken (by decide) (by decide) SourceFloors200000.floor032
  · exact weaken (by decide) (by decide) SourceFloors200000.floor011
  · exact weaken (by decide) (by decide) SourceFloors200000.floor134
  · exact weaken (by decide) (by decide) SourceFloors200000.floor119
  · exact weaken (by decide) (by decide) SourceFloors200000.floor101
  · exact weaken (by decide) (by decide) SourceFloors200000.floor083
  · exact weaken (by decide) (by decide) SourceFloors200000.floor060
  · exact weaken (by decide) (by decide) SourceFloors200000.floor040
  · exact weaken (by decide) (by decide) SourceFloors200000.floor017
  · exact weaken (by decide) (by decide) SourceFloors200000.floor137
  · exact weaken (by decide) (by decide) SourceFloors200000.floor123
  · exact weaken (by decide) (by decide) SourceFloors200000.floor109
  · exact weaken (by decide) (by decide) SourceFloors200000.floor091
  · exact weaken (by decide) (by decide) SourceFloors200000.floor066
  · exact weaken (by decide) (by decide) SourceFloors200000.floor044
  · exact weaken (by decide) (by decide) SourceFloors200000.floor020
  · exact weaken (by decide) (by decide) SourceFloors200000.floor140
  · exact weaken (by decide) (by decide) SourceFloors200000.floor128
  · exact weaken (by decide) (by decide) SourceFloors200000.floor113
  · exact weaken (by decide) (by decide) SourceFloors200000.floor096
  · exact weaken (by decide) (by decide) SourceFloors200000.floor076
  · exact weaken (by decide) (by decide) SourceFloors200000.floor049
  · exact weaken (by decide) (by decide) SourceFloors200000.floor023
  · exact weaken (by decide) (by decide) SourceFloors200000.floor143
  · exact weaken (by decide) (by decide) SourceFloors200000.floor131
  · exact weaken (by decide) (by decide) SourceFloors200000.floor116
  · exact weaken (by decide) (by decide) SourceFloors200000.floor100
  · exact weaken (by decide) (by decide) SourceFloors200000.floor080
  · exact weaken (by decide) (by decide) SourceFloors200000.floor052
  · exact weaken (by decide) (by decide) SourceFloors200000.floor023

#print axioms floors
end JSP233.SourceQueryFloors200000G2
