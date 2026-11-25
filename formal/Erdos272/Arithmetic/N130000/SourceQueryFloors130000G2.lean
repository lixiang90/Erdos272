module

public import Erdos272.Arithmetic.N130000.SourceQueryData130000
public import Erdos272.Arithmetic.N130000.SourceFloors130000

@[expose] public section

namespace JSP233.SourceQueryFloors130000G2
open SourceQueryData130000 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hlo : 254 ≤ i) (hhi : i < 311) :
    Floor (query i).lower (query i).cutoff (query i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors130000.floor024
  · exact weaken (by decide) (by decide) SourceFloors130000.floor054
  · exact weaken (by decide) (by decide) SourceFloors130000.floor034
  · exact weaken (by decide) (by decide) SourceFloors130000.floor013
  · exact weaken (by decide) (by decide) SourceFloors130000.floor002
  · exact weaken (by decide) (by decide) SourceFloors130000.floor002
  · exact weaken (by decide) (by decide) SourceFloors130000.floor002
  · exact weaken (by decide) (by decide) SourceFloors130000.floor002
  · exact weaken (by decide) (by decide) SourceFloors130000.floor114
  · exact weaken (by decide) (by decide) SourceFloors130000.floor083
  · exact weaken (by decide) (by decide) SourceFloors130000.floor046
  · exact weaken (by decide) (by decide) SourceFloors130000.floor005
  · exact weaken (by decide) (by decide) SourceFloors130000.floor005
  · exact weaken (by decide) (by decide) SourceFloors130000.floor005
  · exact weaken (by decide) (by decide) SourceFloors130000.floor005
  · exact weaken (by decide) (by decide) SourceFloors130000.floor125
  · exact weaken (by decide) (by decide) SourceFloors130000.floor091
  · exact weaken (by decide) (by decide) SourceFloors130000.floor056
  · exact weaken (by decide) (by decide) SourceFloors130000.floor009
  · exact weaken (by decide) (by decide) SourceFloors130000.floor009
  · exact weaken (by decide) (by decide) SourceFloors130000.floor009
  · exact weaken (by decide) (by decide) SourceFloors130000.floor009
  · exact weaken (by decide) (by decide) SourceFloors130000.floor140
  · exact weaken (by decide) (by decide) SourceFloors130000.floor109
  · exact weaken (by decide) (by decide) SourceFloors130000.floor065
  · exact weaken (by decide) (by decide) SourceFloors130000.floor036
  · exact weaken (by decide) (by decide) SourceFloors130000.floor009
  · exact weaken (by decide) (by decide) SourceFloors130000.floor009
  · exact weaken (by decide) (by decide) SourceFloors130000.floor009
  · exact weaken (by decide) (by decide) SourceFloors130000.floor148
  · exact weaken (by decide) (by decide) SourceFloors130000.floor117
  · exact weaken (by decide) (by decide) SourceFloors130000.floor073
  · exact weaken (by decide) (by decide) SourceFloors130000.floor040
  · exact weaken (by decide) (by decide) SourceFloors130000.floor016
  · exact weaken (by decide) (by decide) SourceFloors130000.floor016
  · exact weaken (by decide) (by decide) SourceFloors130000.floor016
  · exact weaken (by decide) (by decide) SourceFloors130000.floor152
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors291012.floor399
  · exact weaken (by decide) (by decide) SourceFloors130000.floor093
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors142758.floor083
  · exact weaken (by decide) (by decide) SourceFloors130000.floor022
  · exact weaken (by decide) (by decide) SourceFloors130000.floor022
  · exact weaken (by decide) (by decide) SourceFloors130000.floor022
  · exact weaken (by decide) (by decide) SourceFloors130000.floor160
  · exact weaken (by decide) (by decide) SourceFloors130000.floor133
  · exact weaken (by decide) (by decide) SourceFloors130000.floor100
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors142758.floor090
  · exact weaken (by decide) (by decide) SourceFloors130000.floor022
  · exact weaken (by decide) (by decide) SourceFloors130000.floor022
  · exact weaken (by decide) (by decide) SourceFloors130000.floor022
  · exact weaken (by decide) (by decide) SourceFloors130000.floor164
  · exact LowResourceBridges3040.floor_weaken_defect (by decide) (by decide) (by decide) SourceFloors155716.floor048
  · exact weaken (by decide) (by decide) SourceFloors130000.floor106
  · exact weaken (by decide) (by decide) SourceFloors130000.floor081
  · exact weaken (by decide) (by decide) SourceFloors130000.floor029
  · exact weaken (by decide) (by decide) SourceFloors130000.floor029
  · exact weaken (by decide) (by decide) SourceFloors130000.floor029

#print axioms floors
end JSP233.SourceQueryFloors130000G2
