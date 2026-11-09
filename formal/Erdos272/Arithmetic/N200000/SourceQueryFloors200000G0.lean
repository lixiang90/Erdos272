module

public import Erdos272.Arithmetic.N200000.SourceQueryData200000
public import Erdos272.Arithmetic.N200000.SourceFloors200000

@[expose] public section

namespace JSP233.SourceQueryFloors200000G0
open SourceQueryData200000 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hlo : 0 ≤ i) (hhi : i < 50) :
    Floor (query i).lower (query i).cutoff (query i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors200000.floor006
  · exact weaken (by decide) (by decide) SourceFloors200000.floor077
  · exact weaken (by decide) (by decide) SourceFloors200000.floor061
  · exact weaken (by decide) (by decide) SourceFloors200000.floor045
  · exact weaken (by decide) (by decide) SourceFloors200000.floor033
  · exact weaken (by decide) (by decide) SourceFloors200000.floor024
  · exact weaken (by decide) (by decide) SourceFloors200000.floor007
  · exact weaken (by decide) (by decide) SourceFloors200000.floor000
  · exact weaken (by decide) (by decide) SourceFloors200000.floor102
  · exact weaken (by decide) (by decide) SourceFloors200000.floor084
  · exact weaken (by decide) (by decide) SourceFloors200000.floor067
  · exact weaken (by decide) (by decide) SourceFloors200000.floor053
  · exact weaken (by decide) (by decide) SourceFloors200000.floor036
  · exact weaken (by decide) (by decide) SourceFloors200000.floor027
  · exact weaken (by decide) (by decide) SourceFloors200000.floor003
  · exact weaken (by decide) (by decide) SourceFloors200000.floor122
  · exact weaken (by decide) (by decide) SourceFloors200000.floor106
  · exact weaken (by decide) (by decide) SourceFloors200000.floor087
  · exact weaken (by decide) (by decide) SourceFloors200000.floor069
  · exact weaken (by decide) (by decide) SourceFloors200000.floor050
  · exact weaken (by decide) (by decide) SourceFloors200000.floor030
  · exact weaken (by decide) (by decide) SourceFloors200000.floor009
  · exact weaken (by decide) (by decide) SourceFloors200000.floor133
  · exact weaken (by decide) (by decide) SourceFloors200000.floor117
  · exact weaken (by decide) (by decide) SourceFloors200000.floor098
  · exact weaken (by decide) (by decide) SourceFloors200000.floor081
  · exact weaken (by decide) (by decide) SourceFloors200000.floor058
  · exact weaken (by decide) (by decide) SourceFloors200000.floor038
  · exact weaken (by decide) (by decide) SourceFloors200000.floor015
  · exact weaken (by decide) (by decide) SourceFloors200000.floor135
  · exact weaken (by decide) (by decide) SourceFloors200000.floor120
  · exact weaken (by decide) (by decide) SourceFloors200000.floor104
  · exact weaken (by decide) (by decide) SourceFloors200000.floor085
  · exact weaken (by decide) (by decide) SourceFloors200000.floor064
  · exact weaken (by decide) (by decide) SourceFloors200000.floor042
  · exact weaken (by decide) (by decide) SourceFloors200000.floor018
  · exact weaken (by decide) (by decide) SourceFloors200000.floor138
  · exact weaken (by decide) (by decide) SourceFloors200000.floor126
  · exact weaken (by decide) (by decide) SourceFloors200000.floor111
  · exact weaken (by decide) (by decide) SourceFloors200000.floor093
  · exact weaken (by decide) (by decide) SourceFloors200000.floor070
  · exact weaken (by decide) (by decide) SourceFloors200000.floor044
  · exact weaken (by decide) (by decide) SourceFloors200000.floor021
  · exact weaken (by decide) (by decide) SourceFloors200000.floor141
  · exact weaken (by decide) (by decide) SourceFloors200000.floor129
  · exact weaken (by decide) (by decide) SourceFloors200000.floor114
  · exact weaken (by decide) (by decide) SourceFloors200000.floor095
  · exact weaken (by decide) (by decide) SourceFloors200000.floor075
  · exact weaken (by decide) (by decide) SourceFloors200000.floor048
  · exact weaken (by decide) (by decide) SourceFloors200000.floor021

#print axioms floors
end JSP233.SourceQueryFloors200000G0
