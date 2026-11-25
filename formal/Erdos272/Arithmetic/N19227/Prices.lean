module

public import Erdos272.Arithmetic.N19227.Floors.From40
public import Erdos272.Arithmetic.N19227.Floors.From48
public import Erdos272.Arithmetic.N20258.IndividualFloors20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def prices : Floor :=
  (select 40 IndividualFloors20258.prices (select 48 floor40 (select 48 IndividualFloors20258.prices (select 56 floor48 IndividualFloors20258.prices))))

end JSP233.Credit19227
