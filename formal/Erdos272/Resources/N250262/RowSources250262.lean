module

public import Erdos272.Arithmetic.N250262.RowGeometry250262
public import Erdos272.Arithmetic.N250262.SourceFloors250262

@[expose] public section

namespace JSP233.RowSources250262
open CleanupRows250262 UnitRecipeStatic208 SourceFloorSound291012
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem sources {k : ℕ} (hk : k < 28) (b : Fin 7) :
    Floor (evalData (data k).row b).T (evalData (data k).row b).E (data k).potential := by
  interval_cases k <;> fin_cases b
  · exact weaken (by decide) (by decide) SourceFloors250262.floor084
  · exact weaken (by decide) (by decide) SourceFloors250262.floor063
  · exact weaken (by decide) (by decide) SourceFloors250262.floor048
  · exact weaken (by decide) (by decide) SourceFloors250262.floor031
  · exact weaken (by decide) (by decide) SourceFloors250262.floor020
  · exact weaken (by decide) (by decide) SourceFloors250262.floor007
  · exact weaken (by decide) (by decide) SourceFloors250262.floor000
  · exact weaken (by decide) (by decide) SourceFloors250262.floor118
  · exact weaken (by decide) (by decide) SourceFloors250262.floor095
  · exact weaken (by decide) (by decide) SourceFloors250262.floor073
  · exact weaken (by decide) (by decide) SourceFloors250262.floor058
  · exact weaken (by decide) (by decide) SourceFloors250262.floor034
  · exact weaken (by decide) (by decide) SourceFloors250262.floor022
  · exact weaken (by decide) (by decide) SourceFloors250262.floor002
  · exact weaken (by decide) (by decide) SourceFloors250262.floor142
  · exact weaken (by decide) (by decide) SourceFloors250262.floor122
  · exact weaken (by decide) (by decide) SourceFloors250262.floor099
  · exact weaken (by decide) (by decide) SourceFloors250262.floor070
  · exact weaken (by decide) (by decide) SourceFloors250262.floor050
  · exact weaken (by decide) (by decide) SourceFloors250262.floor028
  · exact weaken (by decide) (by decide) SourceFloors250262.floor009
  · exact weaken (by decide) (by decide) SourceFloors250262.floor159
  · exact weaken (by decide) (by decide) SourceFloors250262.floor136
  · exact weaken (by decide) (by decide) SourceFloors250262.floor112
  · exact weaken (by decide) (by decide) SourceFloors250262.floor092
  · exact weaken (by decide) (by decide) SourceFloors250262.floor064
  · exact weaken (by decide) (by decide) SourceFloors250262.floor037
  · exact weaken (by decide) (by decide) SourceFloors250262.floor012
  · exact weaken (by decide) (by decide) SourceFloors250262.floor163
  · exact weaken (by decide) (by decide) SourceFloors250262.floor147
  · exact weaken (by decide) (by decide) SourceFloors250262.floor127
  · exact weaken (by decide) (by decide) SourceFloors250262.floor103
  · exact weaken (by decide) (by decide) SourceFloors250262.floor068
  · exact weaken (by decide) (by decide) SourceFloors250262.floor041
  · exact weaken (by decide) (by decide) SourceFloors250262.floor015
  · exact weaken (by decide) (by decide) SourceFloors250262.floor165
  · exact weaken (by decide) (by decide) SourceFloors250262.floor149
  · exact weaken (by decide) (by decide) SourceFloors250262.floor129
  · exact weaken (by decide) (by decide) SourceFloors250262.floor106
  · exact weaken (by decide) (by decide) SourceFloors250262.floor079
  · exact weaken (by decide) (by decide) SourceFloors250262.floor045
  · exact weaken (by decide) (by decide) SourceFloors250262.floor015
  · exact weaken (by decide) (by decide) SourceFloors250262.floor169
  · exact weaken (by decide) (by decide) SourceFloors250262.floor156
  · exact weaken (by decide) (by decide) SourceFloors250262.floor137
  · exact weaken (by decide) (by decide) SourceFloors250262.floor111
  · exact weaken (by decide) (by decide) SourceFloors250262.floor086
  · exact weaken (by decide) (by decide) SourceFloors250262.floor053
  · exact weaken (by decide) (by decide) SourceFloors250262.floor016
  · exact weaken (by decide) (by decide) SourceFloors250262.floor088
  · exact weaken (by decide) (by decide) SourceFloors250262.floor067
  · exact weaken (by decide) (by decide) SourceFloors250262.floor049
  · exact weaken (by decide) (by decide) SourceFloors250262.floor033
  · exact weaken (by decide) (by decide) SourceFloors250262.floor026
  · exact weaken (by decide) (by decide) SourceFloors250262.floor008
  · exact weaken (by decide) (by decide) SourceFloors250262.floor001
  · exact weaken (by decide) (by decide) SourceFloors250262.floor119
  · exact weaken (by decide) (by decide) SourceFloors250262.floor096
  · exact weaken (by decide) (by decide) SourceFloors250262.floor074
  · exact weaken (by decide) (by decide) SourceFloors250262.floor059
  · exact weaken (by decide) (by decide) SourceFloors250262.floor035
  · exact weaken (by decide) (by decide) SourceFloors250262.floor023
  · exact weaken (by decide) (by decide) SourceFloors250262.floor003
  · exact weaken (by decide) (by decide) SourceFloors250262.floor141
  · exact weaken (by decide) (by decide) SourceFloors250262.floor123
  · exact weaken (by decide) (by decide) SourceFloors250262.floor100
  · exact weaken (by decide) (by decide) SourceFloors250262.floor071
  · exact weaken (by decide) (by decide) SourceFloors250262.floor051
  · exact weaken (by decide) (by decide) SourceFloors250262.floor027
  · exact weaken (by decide) (by decide) SourceFloors250262.floor006
  · exact weaken (by decide) (by decide) SourceFloors250262.floor153
  · exact weaken (by decide) (by decide) SourceFloors250262.floor132
  · exact weaken (by decide) (by decide) SourceFloors250262.floor110
  · exact weaken (by decide) (by decide) SourceFloors250262.floor089
  · exact weaken (by decide) (by decide) SourceFloors250262.floor062
  · exact weaken (by decide) (by decide) SourceFloors250262.floor037
  · exact weaken (by decide) (by decide) SourceFloors250262.floor012
  · exact weaken (by decide) (by decide) SourceFloors250262.floor162
  · exact weaken (by decide) (by decide) SourceFloors250262.floor145
  · exact weaken (by decide) (by decide) SourceFloors250262.floor127
  · exact weaken (by decide) (by decide) SourceFloors250262.floor103
  · exact weaken (by decide) (by decide) SourceFloors250262.floor068
  · exact weaken (by decide) (by decide) SourceFloors250262.floor041
  · exact weaken (by decide) (by decide) SourceFloors250262.floor015
  · exact weaken (by decide) (by decide) SourceFloors250262.floor167
  · exact weaken (by decide) (by decide) SourceFloors250262.floor151
  · exact weaken (by decide) (by decide) SourceFloors250262.floor131
  · exact weaken (by decide) (by decide) SourceFloors250262.floor107
  · exact weaken (by decide) (by decide) SourceFloors250262.floor082
  · exact weaken (by decide) (by decide) SourceFloors250262.floor046
  · exact weaken (by decide) (by decide) SourceFloors250262.floor017
  · exact weaken (by decide) (by decide) SourceFloors250262.floor170
  · exact weaken (by decide) (by decide) SourceFloors250262.floor157
  · exact weaken (by decide) (by decide) SourceFloors250262.floor138
  · exact weaken (by decide) (by decide) SourceFloors250262.floor115
  · exact weaken (by decide) (by decide) SourceFloors250262.floor087
  · exact weaken (by decide) (by decide) SourceFloors250262.floor055
  · exact weaken (by decide) (by decide) SourceFloors250262.floor017
  · exact weaken (by decide) (by decide) SourceFloors250262.floor081
  · exact weaken (by decide) (by decide) SourceFloors250262.floor063
  · exact weaken (by decide) (by decide) SourceFloors250262.floor044
  · exact weaken (by decide) (by decide) SourceFloors250262.floor031
  · exact weaken (by decide) (by decide) SourceFloors250262.floor020
  · exact weaken (by decide) (by decide) SourceFloors250262.floor008
  · exact weaken (by decide) (by decide) SourceFloors250262.floor001
  · exact weaken (by decide) (by decide) SourceFloors250262.floor120
  · exact weaken (by decide) (by decide) SourceFloors250262.floor097
  · exact weaken (by decide) (by decide) SourceFloors250262.floor075
  · exact weaken (by decide) (by decide) SourceFloors250262.floor060
  · exact weaken (by decide) (by decide) SourceFloors250262.floor036
  · exact weaken (by decide) (by decide) SourceFloors250262.floor024
  · exact weaken (by decide) (by decide) SourceFloors250262.floor004
  · exact weaken (by decide) (by decide) SourceFloors250262.floor143
  · exact weaken (by decide) (by decide) SourceFloors250262.floor124
  · exact weaken (by decide) (by decide) SourceFloors250262.floor101
  · exact weaken (by decide) (by decide) SourceFloors250262.floor077
  · exact weaken (by decide) (by decide) SourceFloors250262.floor052
  · exact weaken (by decide) (by decide) SourceFloors250262.floor029
  · exact weaken (by decide) (by decide) SourceFloors250262.floor010
  · exact weaken (by decide) (by decide) SourceFloors250262.floor154
  · exact weaken (by decide) (by decide) SourceFloors250262.floor134
  · exact weaken (by decide) (by decide) SourceFloors250262.floor113
  · exact weaken (by decide) (by decide) SourceFloors250262.floor093
  · exact weaken (by decide) (by decide) SourceFloors250262.floor065
  · exact weaken (by decide) (by decide) SourceFloors250262.floor038
  · exact weaken (by decide) (by decide) SourceFloors250262.floor013
  · exact weaken (by decide) (by decide) SourceFloors250262.floor161
  · exact weaken (by decide) (by decide) SourceFloors250262.floor146
  · exact weaken (by decide) (by decide) SourceFloors250262.floor126
  · exact weaken (by decide) (by decide) SourceFloors250262.floor104
  · exact weaken (by decide) (by decide) SourceFloors250262.floor069
  · exact weaken (by decide) (by decide) SourceFloors250262.floor042
  · exact weaken (by decide) (by decide) SourceFloors250262.floor015
  · exact weaken (by decide) (by decide) SourceFloors250262.floor166
  · exact weaken (by decide) (by decide) SourceFloors250262.floor150
  · exact weaken (by decide) (by decide) SourceFloors250262.floor130
  · exact weaken (by decide) (by decide) SourceFloors250262.floor108
  · exact weaken (by decide) (by decide) SourceFloors250262.floor080
  · exact weaken (by decide) (by decide) SourceFloors250262.floor047
  · exact weaken (by decide) (by decide) SourceFloors250262.floor018
  · exact weaken (by decide) (by decide) SourceFloors250262.floor171
  · exact weaken (by decide) (by decide) SourceFloors250262.floor158
  · exact weaken (by decide) (by decide) SourceFloors250262.floor139
  · exact weaken (by decide) (by decide) SourceFloors250262.floor116
  · exact weaken (by decide) (by decide) SourceFloors250262.floor090
  · exact weaken (by decide) (by decide) SourceFloors250262.floor056
  · exact weaken (by decide) (by decide) SourceFloors250262.floor018
  · exact weaken (by decide) (by decide) SourceFloors250262.floor085
  · exact weaken (by decide) (by decide) SourceFloors250262.floor067
  · exact weaken (by decide) (by decide) SourceFloors250262.floor049
  · exact weaken (by decide) (by decide) SourceFloors250262.floor032
  · exact weaken (by decide) (by decide) SourceFloors250262.floor021
  · exact weaken (by decide) (by decide) SourceFloors250262.floor008
  · exact weaken (by decide) (by decide) SourceFloors250262.floor001
  · exact weaken (by decide) (by decide) SourceFloors250262.floor121
  · exact weaken (by decide) (by decide) SourceFloors250262.floor098
  · exact weaken (by decide) (by decide) SourceFloors250262.floor076
  · exact weaken (by decide) (by decide) SourceFloors250262.floor061
  · exact weaken (by decide) (by decide) SourceFloors250262.floor040
  · exact weaken (by decide) (by decide) SourceFloors250262.floor025
  · exact weaken (by decide) (by decide) SourceFloors250262.floor005
  · exact weaken (by decide) (by decide) SourceFloors250262.floor144
  · exact weaken (by decide) (by decide) SourceFloors250262.floor125
  · exact weaken (by decide) (by decide) SourceFloors250262.floor102
  · exact weaken (by decide) (by decide) SourceFloors250262.floor078
  · exact weaken (by decide) (by decide) SourceFloors250262.floor054
  · exact weaken (by decide) (by decide) SourceFloors250262.floor030
  · exact weaken (by decide) (by decide) SourceFloors250262.floor011
  · exact weaken (by decide) (by decide) SourceFloors250262.floor155
  · exact weaken (by decide) (by decide) SourceFloors250262.floor135
  · exact weaken (by decide) (by decide) SourceFloors250262.floor114
  · exact weaken (by decide) (by decide) SourceFloors250262.floor094
  · exact weaken (by decide) (by decide) SourceFloors250262.floor066
  · exact weaken (by decide) (by decide) SourceFloors250262.floor039
  · exact weaken (by decide) (by decide) SourceFloors250262.floor014
  · exact weaken (by decide) (by decide) SourceFloors250262.floor164
  · exact weaken (by decide) (by decide) SourceFloors250262.floor148
  · exact weaken (by decide) (by decide) SourceFloors250262.floor128
  · exact weaken (by decide) (by decide) SourceFloors250262.floor105
  · exact weaken (by decide) (by decide) SourceFloors250262.floor072
  · exact weaken (by decide) (by decide) SourceFloors250262.floor043
  · exact weaken (by decide) (by decide) SourceFloors250262.floor015
  · exact weaken (by decide) (by decide) SourceFloors250262.floor168
  · exact weaken (by decide) (by decide) SourceFloors250262.floor152
  · exact weaken (by decide) (by decide) SourceFloors250262.floor133
  · exact weaken (by decide) (by decide) SourceFloors250262.floor109
  · exact weaken (by decide) (by decide) SourceFloors250262.floor083
  · exact weaken (by decide) (by decide) SourceFloors250262.floor053
  · exact weaken (by decide) (by decide) SourceFloors250262.floor019
  · exact weaken (by decide) (by decide) SourceFloors250262.floor172
  · exact weaken (by decide) (by decide) SourceFloors250262.floor160
  · exact weaken (by decide) (by decide) SourceFloors250262.floor140
  · exact weaken (by decide) (by decide) SourceFloors250262.floor117
  · exact weaken (by decide) (by decide) SourceFloors250262.floor091
  · exact weaken (by decide) (by decide) SourceFloors250262.floor057
  · exact weaken (by decide) (by decide) SourceFloors250262.floor019

#print axioms sources
end
end JSP233.RowSources250262
