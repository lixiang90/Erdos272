module

public import Erdos272.Arithmetic.N243614.RowGeometry243614
public import Erdos272.Arithmetic.N243614.SourceFloors243614

@[expose] public section

namespace JSP233.RowSources243614
open CleanupRows243614 UnitRecipeStatic208 SourceFloorSound291012
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem sources {k : ℕ} (hk : k < 5) (b : Fin 7) :
    Floor (evalData (data k).row b).T (evalData (data k).row b).E (data k).potential := by
  interval_cases k <;> fin_cases b
  · exact weaken (by decide) (by decide) SourceFloors243614.floor020
  · exact weaken (by decide) (by decide) SourceFloors243614.floor016
  · exact weaken (by decide) (by decide) SourceFloors243614.floor012
  · exact weaken (by decide) (by decide) SourceFloors243614.floor009
  · exact weaken (by decide) (by decide) SourceFloors243614.floor005
  · exact weaken (by decide) (by decide) SourceFloors243614.floor003
  · exact weaken (by decide) (by decide) SourceFloors243614.floor000
  · exact weaken (by decide) (by decide) SourceFloors243614.floor026
  · exact weaken (by decide) (by decide) SourceFloors243614.floor022
  · exact weaken (by decide) (by decide) SourceFloors243614.floor019
  · exact weaken (by decide) (by decide) SourceFloors243614.floor015
  · exact weaken (by decide) (by decide) SourceFloors243614.floor010
  · exact weaken (by decide) (by decide) SourceFloors243614.floor006
  · exact weaken (by decide) (by decide) SourceFloors243614.floor001
  · exact weaken (by decide) (by decide) SourceFloors243614.floor030
  · exact weaken (by decide) (by decide) SourceFloors243614.floor027
  · exact weaken (by decide) (by decide) SourceFloors243614.floor023
  · exact weaken (by decide) (by decide) SourceFloors243614.floor017
  · exact weaken (by decide) (by decide) SourceFloors243614.floor013
  · exact weaken (by decide) (by decide) SourceFloors243614.floor008
  · exact weaken (by decide) (by decide) SourceFloors243614.floor002
  · exact weaken (by decide) (by decide) SourceFloors243614.floor033
  · exact weaken (by decide) (by decide) SourceFloors243614.floor031
  · exact weaken (by decide) (by decide) SourceFloors243614.floor028
  · exact weaken (by decide) (by decide) SourceFloors243614.floor024
  · exact weaken (by decide) (by decide) SourceFloors243614.floor018
  · exact weaken (by decide) (by decide) SourceFloors243614.floor011
  · exact weaken (by decide) (by decide) SourceFloors243614.floor004
  · exact weaken (by decide) (by decide) SourceFloors243614.floor034
  · exact weaken (by decide) (by decide) SourceFloors243614.floor032
  · exact weaken (by decide) (by decide) SourceFloors243614.floor029
  · exact weaken (by decide) (by decide) SourceFloors243614.floor025
  · exact weaken (by decide) (by decide) SourceFloors243614.floor021
  · exact weaken (by decide) (by decide) SourceFloors243614.floor014
  · exact weaken (by decide) (by decide) SourceFloors243614.floor007

#print axioms sources
end
end JSP233.RowSources243614
