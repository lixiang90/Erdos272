module

public import Erdos272.Arithmetic.N233811.RowGeometry233811
public import Erdos272.Arithmetic.N233811.SourceFloors233811

@[expose] public section

namespace JSP233.RowSources233811
open CleanupRows233811 UnitRecipeStatic208 SourceFloorSound291012
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem sources {k : ℕ} (hk : k < 12) (b : Fin 7) :
    Floor (evalData (data k).row b).T (evalData (data k).row b).E (data k).potential := by
  interval_cases k <;> fin_cases b
  · exact weaken (by decide) (by decide) SourceFloors233811.floor045
  · exact weaken (by decide) (by decide) SourceFloors233811.floor036
  · exact weaken (by decide) (by decide) SourceFloors233811.floor027
  · exact weaken (by decide) (by decide) SourceFloors233811.floor020
  · exact weaken (by decide) (by decide) SourceFloors233811.floor012
  · exact weaken (by decide) (by decide) SourceFloors233811.floor004
  · exact weaken (by decide) (by decide) SourceFloors233811.floor000
  · exact weaken (by decide) (by decide) SourceFloors233811.floor061
  · exact weaken (by decide) (by decide) SourceFloors233811.floor051
  · exact weaken (by decide) (by decide) SourceFloors233811.floor041
  · exact weaken (by decide) (by decide) SourceFloors233811.floor034
  · exact weaken (by decide) (by decide) SourceFloors233811.floor022
  · exact weaken (by decide) (by decide) SourceFloors233811.floor014
  · exact weaken (by decide) (by decide) SourceFloors233811.floor002
  · exact weaken (by decide) (by decide) SourceFloors233811.floor071
  · exact weaken (by decide) (by decide) SourceFloors233811.floor063
  · exact weaken (by decide) (by decide) SourceFloors233811.floor053
  · exact weaken (by decide) (by decide) SourceFloors233811.floor043
  · exact weaken (by decide) (by decide) SourceFloors233811.floor030
  · exact weaken (by decide) (by decide) SourceFloors233811.floor018
  · exact weaken (by decide) (by decide) SourceFloors233811.floor006
  · exact weaken (by decide) (by decide) SourceFloors233811.floor076
  · exact weaken (by decide) (by decide) SourceFloors233811.floor068
  · exact weaken (by decide) (by decide) SourceFloors233811.floor058
  · exact weaken (by decide) (by decide) SourceFloors233811.floor050
  · exact weaken (by decide) (by decide) SourceFloors233811.floor038
  · exact weaken (by decide) (by decide) SourceFloors233811.floor024
  · exact weaken (by decide) (by decide) SourceFloors233811.floor008
  · exact weaken (by decide) (by decide) SourceFloors233811.floor079
  · exact weaken (by decide) (by decide) SourceFloors233811.floor073
  · exact weaken (by decide) (by decide) SourceFloors233811.floor065
  · exact weaken (by decide) (by decide) SourceFloors233811.floor055
  · exact weaken (by decide) (by decide) SourceFloors233811.floor039
  · exact weaken (by decide) (by decide) SourceFloors233811.floor025
  · exact weaken (by decide) (by decide) SourceFloors233811.floor009
  · exact weaken (by decide) (by decide) SourceFloors233811.floor081
  · exact weaken (by decide) (by decide) SourceFloors233811.floor075
  · exact weaken (by decide) (by decide) SourceFloors233811.floor067
  · exact weaken (by decide) (by decide) SourceFloors233811.floor057
  · exact weaken (by decide) (by decide) SourceFloors233811.floor047
  · exact weaken (by decide) (by decide) SourceFloors233811.floor029
  · exact weaken (by decide) (by decide) SourceFloors233811.floor011
  · exact weaken (by decide) (by decide) SourceFloors233811.floor082
  · exact weaken (by decide) (by decide) SourceFloors233811.floor077
  · exact weaken (by decide) (by decide) SourceFloors233811.floor069
  · exact weaken (by decide) (by decide) SourceFloors233811.floor059
  · exact weaken (by decide) (by decide) SourceFloors233811.floor048
  · exact weaken (by decide) (by decide) SourceFloors233811.floor032
  · exact weaken (by decide) (by decide) SourceFloors233811.floor016
  · exact weaken (by decide) (by decide) SourceFloors233811.floor046
  · exact weaken (by decide) (by decide) SourceFloors233811.floor037
  · exact weaken (by decide) (by decide) SourceFloors233811.floor028
  · exact weaken (by decide) (by decide) SourceFloors233811.floor021
  · exact weaken (by decide) (by decide) SourceFloors233811.floor013
  · exact weaken (by decide) (by decide) SourceFloors233811.floor005
  · exact weaken (by decide) (by decide) SourceFloors233811.floor001
  · exact weaken (by decide) (by decide) SourceFloors233811.floor062
  · exact weaken (by decide) (by decide) SourceFloors233811.floor052
  · exact weaken (by decide) (by decide) SourceFloors233811.floor042
  · exact weaken (by decide) (by decide) SourceFloors233811.floor035
  · exact weaken (by decide) (by decide) SourceFloors233811.floor023
  · exact weaken (by decide) (by decide) SourceFloors233811.floor015
  · exact weaken (by decide) (by decide) SourceFloors233811.floor003
  · exact weaken (by decide) (by decide) SourceFloors233811.floor072
  · exact weaken (by decide) (by decide) SourceFloors233811.floor064
  · exact weaken (by decide) (by decide) SourceFloors233811.floor054
  · exact weaken (by decide) (by decide) SourceFloors233811.floor044
  · exact weaken (by decide) (by decide) SourceFloors233811.floor031
  · exact weaken (by decide) (by decide) SourceFloors233811.floor019
  · exact weaken (by decide) (by decide) SourceFloors233811.floor007
  · exact weaken (by decide) (by decide) SourceFloors233811.floor080
  · exact weaken (by decide) (by decide) SourceFloors233811.floor074
  · exact weaken (by decide) (by decide) SourceFloors233811.floor066
  · exact weaken (by decide) (by decide) SourceFloors233811.floor056
  · exact weaken (by decide) (by decide) SourceFloors233811.floor040
  · exact weaken (by decide) (by decide) SourceFloors233811.floor026
  · exact weaken (by decide) (by decide) SourceFloors233811.floor010
  · exact weaken (by decide) (by decide) SourceFloors233811.floor083
  · exact weaken (by decide) (by decide) SourceFloors233811.floor078
  · exact weaken (by decide) (by decide) SourceFloors233811.floor070
  · exact weaken (by decide) (by decide) SourceFloors233811.floor060
  · exact weaken (by decide) (by decide) SourceFloors233811.floor049
  · exact weaken (by decide) (by decide) SourceFloors233811.floor033
  · exact weaken (by decide) (by decide) SourceFloors233811.floor017

#print axioms sources
end
end JSP233.RowSources233811
