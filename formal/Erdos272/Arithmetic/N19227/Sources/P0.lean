module

public import Erdos272.Arithmetic.N19227.Prices
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def p0 : Source := ⟨⟨43,82,14,2000,100,[
  (.marks 43 1 48 false,1501),
  (.marks 43 1 54 false,2001),
  (.marks 43 1 57 false,901),
  (.marks 43 1 60 false,3701),
  (.marks 43 1 63 false,3501),
  (.marks 43 1 66 false,13001),
  (.marks 43 1 69 false,9801),
  (.marks 43 1 72 false,16201),
  (.marks 43 1 75 false,11001),
  (.marks 43 1 78 false,15801),
  (.marks 43 1 81 false,12401),
  (.marks 43 1 82 false,2201),
  (.marks 43 2 48 false,568),
  (.marks 43 2 54 false,4935),
  (.marks 43 2 57 false,7701),
  (.marks 43 2 60 false,9301),
  (.marks 43 2 63 false,6101),
  (.marks 43 3 48 false,1835),
  (.marks 43 3 51 false,8201),
  (.marks 43 3 54 false,3668),
  (.marks 43 4 45 false,2041),
  (.marks 43 4 48 false,5301),
  (.marks 43 5 43 false,2001),
  (.marks 43 5 45 false,2361)]⟩,[]⟩

private theorem part43 : Window p0.plan p0.extras 43 50 :=
  window (g:=prices) (by decide +kernel)
private theorem part51 : Window p0.plan p0.extras 51 58 :=
  window (g:=prices) (by decide +kernel)
private theorem part59 : Window p0.plan p0.extras 59 66 :=
  window (g:=prices) (by decide +kernel)
private theorem part67 : Window p0.plan p0.extras 67 74 :=
  window (g:=prices) (by decide +kernel)
private theorem part75 : Window p0.plan p0.extras 75 82 :=
  window (g:=prices) (by decide +kernel)

theorem p0_valid : p0.Valid := by
  change p0.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join part43 part51) (join part59 (join part67 part75)))

end JSP233.Credit19227
