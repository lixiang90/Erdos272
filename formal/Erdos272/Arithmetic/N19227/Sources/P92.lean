module

public import Erdos272.Arithmetic.N19227.Prices
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def p92 : Source := ⟨⟨42,82,14,2000,100,[
  (.marks 42 1 42 false,1401),
  (.marks 42 1 47 false,701),
  (.marks 42 1 50 false,1501),
  (.marks 42 1 53 false,901),
  (.marks 42 1 56 false,1901),
  (.marks 42 1 62 false,3901),
  (.marks 42 1 65 false,9801),
  (.marks 42 1 68 false,13801),
  (.marks 42 1 71 false,11601),
  (.marks 42 1 74 false,14401),
  (.marks 42 1 77 false,11801),
  (.marks 42 1 80 false,16001),
  (.marks 42 1 82 false,6201),
  (.marks 42 2 42 false,901),
  (.marks 42 2 44 false,101),
  (.marks 42 2 47 false,301),
  (.marks 42 2 50 false,701),
  (.marks 42 2 53 false,1501),
  (.marks 42 2 56 false,7601),
  (.marks 42 2 59 false,10101),
  (.marks 42 2 62 false,8301),
  (.marks 42 3 44 false,151),
  (.marks 42 3 47 false,251),
  (.marks 42 3 50 false,6401),
  (.marks 42 3 53 false,6801),
  (.marks 42 4 42 false,201),
  (.marks 42 4 44 false,411),
  (.marks 42 4 47 false,6631),
  (.marks 42 4 50 false,401),
  (.marks 42 5 44 false,3841),
  (.marks 42 5 47 false,321),
  (.marks 42 6 42 false,1001),
  (.marks 42 6 44 false,201)]⟩,[]⟩

private theorem part42 : Window p92.plan p92.extras 42 49 :=
  window (g:=prices) (by decide +kernel)
private theorem part50 : Window p92.plan p92.extras 50 57 :=
  window (g:=prices) (by decide +kernel)
private theorem part58 : Window p92.plan p92.extras 58 65 :=
  window (g:=prices) (by decide +kernel)
private theorem part66 : Window p92.plan p92.extras 66 73 :=
  window (g:=prices) (by decide +kernel)
private theorem part74 : Window p92.plan p92.extras 74 81 :=
  window (g:=prices) (by decide +kernel)
private theorem part82 : Window p92.plan p92.extras 82 82 :=
  window (g:=prices) (by decide +kernel)

theorem p92_valid : p92.Valid := by
  change p92.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join part42 (join part50 part58)) (join part66 (join part74 part82)))

end JSP233.Credit19227
