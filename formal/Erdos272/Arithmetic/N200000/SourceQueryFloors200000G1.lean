module

public import Erdos272.Arithmetic.N200000.SourceQueryData200000
public import Erdos272.Arithmetic.N200000.SourceFloors200000

@[expose] public section

namespace JSP233.SourceQueryFloors200000G1
open SourceQueryData200000 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hlo : 50 ≤ i) (hhi : i < 100) :
    Floor (query i).lower (query i).cutoff (query i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors200000.floor012
  · exact weaken (by decide) (by decide) SourceFloors200000.floor078
  · exact weaken (by decide) (by decide) SourceFloors200000.floor062
  · exact weaken (by decide) (by decide) SourceFloors200000.floor046
  · exact weaken (by decide) (by decide) SourceFloors200000.floor034
  · exact weaken (by decide) (by decide) SourceFloors200000.floor025
  · exact weaken (by decide) (by decide) SourceFloors200000.floor014
  · exact weaken (by decide) (by decide) SourceFloors200000.floor001
  · exact weaken (by decide) (by decide) SourceFloors200000.floor103
  · exact weaken (by decide) (by decide) SourceFloors200000.floor086
  · exact weaken (by decide) (by decide) SourceFloors200000.floor068
  · exact weaken (by decide) (by decide) SourceFloors200000.floor054
  · exact weaken (by decide) (by decide) SourceFloors200000.floor037
  · exact weaken (by decide) (by decide) SourceFloors200000.floor028
  · exact weaken (by decide) (by decide) SourceFloors200000.floor004
  · exact weaken (by decide) (by decide) SourceFloors200000.floor124
  · exact weaken (by decide) (by decide) SourceFloors200000.floor108
  · exact weaken (by decide) (by decide) SourceFloors200000.floor090
  · exact weaken (by decide) (by decide) SourceFloors200000.floor073
  · exact weaken (by decide) (by decide) SourceFloors200000.floor055
  · exact weaken (by decide) (by decide) SourceFloors200000.floor031
  · exact weaken (by decide) (by decide) SourceFloors200000.floor010
  · exact weaken (by decide) (by decide) SourceFloors200000.floor132
  · exact weaken (by decide) (by decide) SourceFloors200000.floor118
  · exact weaken (by decide) (by decide) SourceFloors200000.floor099
  · exact weaken (by decide) (by decide) SourceFloors200000.floor082
  · exact weaken (by decide) (by decide) SourceFloors200000.floor059
  · exact weaken (by decide) (by decide) SourceFloors200000.floor039
  · exact weaken (by decide) (by decide) SourceFloors200000.floor016
  · exact weaken (by decide) (by decide) SourceFloors200000.floor136
  · exact weaken (by decide) (by decide) SourceFloors200000.floor121
  · exact weaken (by decide) (by decide) SourceFloors200000.floor107
  · exact weaken (by decide) (by decide) SourceFloors200000.floor088
  · exact weaken (by decide) (by decide) SourceFloors200000.floor065
  · exact weaken (by decide) (by decide) SourceFloors200000.floor043
  · exact weaken (by decide) (by decide) SourceFloors200000.floor019
  · exact weaken (by decide) (by decide) SourceFloors200000.floor139
  · exact weaken (by decide) (by decide) SourceFloors200000.floor127
  · exact weaken (by decide) (by decide) SourceFloors200000.floor112
  · exact weaken (by decide) (by decide) SourceFloors200000.floor094
  · exact weaken (by decide) (by decide) SourceFloors200000.floor071
  · exact weaken (by decide) (by decide) SourceFloors200000.floor048
  · exact weaken (by decide) (by decide) SourceFloors200000.floor022
  · exact weaken (by decide) (by decide) SourceFloors200000.floor142
  · exact weaken (by decide) (by decide) SourceFloors200000.floor130
  · exact weaken (by decide) (by decide) SourceFloors200000.floor115
  · exact weaken (by decide) (by decide) SourceFloors200000.floor097
  · exact weaken (by decide) (by decide) SourceFloors200000.floor076
  · exact weaken (by decide) (by decide) SourceFloors200000.floor051
  · exact weaken (by decide) (by decide) SourceFloors200000.floor022

#print axioms floors
end JSP233.SourceQueryFloors200000G1
