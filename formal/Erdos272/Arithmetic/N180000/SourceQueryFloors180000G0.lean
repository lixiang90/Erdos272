module

public import Erdos272.Arithmetic.N180000.SourceQueryData180000
public import Erdos272.Arithmetic.N180000.SourceFloors180000

@[expose] public section

namespace JSP233.SourceQueryFloors180000G0
open SourceQueryData180000 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hlo : 0 ≤ i) (hhi : i < 50) :
    Floor (query i).lower (query i).cutoff (query i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors180000.floor009
  · exact weaken (by decide) (by decide) SourceFloors180000.floor064
  · exact weaken (by decide) (by decide) SourceFloors180000.floor051
  · exact weaken (by decide) (by decide) SourceFloors180000.floor042
  · exact weaken (by decide) (by decide) SourceFloors180000.floor030
  · exact weaken (by decide) (by decide) SourceFloors180000.floor021
  · exact weaken (by decide) (by decide) SourceFloors180000.floor012
  · exact weaken (by decide) (by decide) SourceFloors180000.floor000
  · exact weaken (by decide) (by decide) SourceFloors180000.floor083
  · exact weaken (by decide) (by decide) SourceFloors180000.floor071
  · exact weaken (by decide) (by decide) SourceFloors180000.floor058
  · exact weaken (by decide) (by decide) SourceFloors180000.floor045
  · exact weaken (by decide) (by decide) SourceFloors180000.floor033
  · exact weaken (by decide) (by decide) SourceFloors180000.floor023
  · exact weaken (by decide) (by decide) SourceFloors180000.floor003
  · exact weaken (by decide) (by decide) SourceFloors180000.floor093
  · exact weaken (by decide) (by decide) SourceFloors180000.floor079
  · exact weaken (by decide) (by decide) SourceFloors180000.floor067
  · exact weaken (by decide) (by decide) SourceFloors180000.floor053
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors291012.floor119
  · exact weaken (by decide) (by decide) SourceFloors180000.floor026
  · exact weaken (by decide) (by decide) SourceFloors180000.floor005
  · exact weaken (by decide) (by decide) SourceFloors180000.floor099
  · exact weaken (by decide) (by decide) SourceFloors180000.floor089
  · exact weaken (by decide) (by decide) SourceFloors180000.floor075
  · exact weaken (by decide) (by decide) SourceFloors180000.floor062
  · exact weaken (by decide) (by decide) SourceFloors180000.floor047
  · exact weaken (by decide) (by decide) SourceFloors180000.floor028
  · exact weaken (by decide) (by decide) SourceFloors180000.floor007
  · exact weaken (by decide) (by decide) SourceFloors180000.floor104
  · exact weaken (by decide) (by decide) SourceFloors180000.floor095
  · exact weaken (by decide) (by decide) SourceFloors180000.floor081
  · exact weaken (by decide) (by decide) SourceFloors180000.floor069
  · exact weaken (by decide) (by decide) SourceFloors180000.floor049
  · exact weaken (by decide) (by decide) SourceFloors180000.floor035
  · exact weaken (by decide) (by decide) SourceFloors180000.floor015
  · exact weaken (by decide) (by decide) SourceFloors180000.floor106
  · exact weaken (by decide) (by decide) SourceFloors180000.floor097
  · exact weaken (by decide) (by decide) SourceFloors180000.floor086
  · exact weaken (by decide) (by decide) SourceFloors180000.floor073
  · exact weaken (by decide) (by decide) SourceFloors180000.floor056
  · exact weaken (by decide) (by decide) SourceFloors180000.floor037
  · exact weaken (by decide) (by decide) SourceFloors180000.floor017
  · exact weaken (by decide) (by decide) SourceFloors180000.floor108
  · exact weaken (by decide) (by decide) SourceFloors180000.floor102
  · exact weaken (by decide) (by decide) SourceFloors180000.floor091
  · exact weaken (by decide) (by decide) SourceFloors180000.floor077
  · exact weaken (by decide) (by decide) SourceFloors180000.floor060
  · exact weaken (by decide) (by decide) SourceFloors180000.floor040
  · exact weaken (by decide) (by decide) SourceFloors180000.floor019

#print axioms floors
end JSP233.SourceQueryFloors180000G0
