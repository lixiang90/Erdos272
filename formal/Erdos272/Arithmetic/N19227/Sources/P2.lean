module

public import Erdos272.Arithmetic.N19227.Prices
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def p2 : Source := ⟨⟨45,100,17,3000,100,[
  (.marks 45 1 47 false,701),
  (.marks 45 1 50 false,1501),
  (.marks 45 1 53 false,901),
  (.marks 45 1 56 false,1901),
  (.marks 45 1 62 false,2501),
  (.marks 45 1 65 false,101),
  (.marks 45 1 68 false,3201),
  (.marks 45 1 71 false,301),
  (.marks 45 1 74 false,2201),
  (.marks 45 1 77 false,7001),
  (.marks 45 1 80 false,16001),
  (.marks 45 1 83 false,14401),
  (.marks 45 1 86 false,15801),
  (.marks 45 1 89 false,15001),
  (.marks 45 1 92 false,17201),
  (.marks 45 1 95 false,14801),
  (.marks 45 1 98 false,19401),
  (.marks 45 1 100 false,9601),
  (.marks 45 2 47 false,301),
  (.marks 45 2 50 false,701),
  (.marks 45 2 53 false,35),
  (.marks 45 2 56 false,601),
  (.marks 45 2 59 false,1035),
  (.marks 45 2 62 false,1035),
  (.marks 45 2 65 false,2568),
  (.marks 45 2 68 false,10601),
  (.marks 45 2 71 false,11301),
  (.marks 45 2 74 false,12201),
  (.marks 45 2 77 false,4801),
  (.marks 45 3 47 false,251),
  (.marks 45 3 50 false,151),
  (.marks 45 3 53 false,818),
  (.marks 45 3 59 false,4768),
  (.marks 45 3 62 false,8668),
  (.marks 45 3 65 false,7135),
  (.marks 45 4 50 false,681),
  (.marks 45 4 53 false,51),
  (.marks 45 4 56 false,7001),
  (.marks 45 4 59 false,4301),
  (.marks 45 5 47 false,118),
  (.marks 45 5 50 false,271),
  (.marks 45 5 53 false,7068),
  (.marks 45 6 47 false,235),
  (.marks 45 6 50 false,4244),
  (.marks 45 6 53 false,335),
  (.marks 45 7 47 false,1576),
  (.marks 45 7 50 false,1459),
  (.marks 45 8 47 false,1871),
  (.marks 45 9 45 false,121),
  (.marks 45 9 47 false,957),
  (.marks 45 10 45 false,909),
  (.marks 45 11 45 false,1174)]⟩,[]⟩

private theorem part45 : Window p2.plan p2.extras 45 52 :=
  window (g:=prices) (by decide +kernel)
private theorem part53 : Window p2.plan p2.extras 53 60 :=
  window (g:=prices) (by decide +kernel)
private theorem part61 : Window p2.plan p2.extras 61 68 :=
  window (g:=prices) (by decide +kernel)
private theorem part69 : Window p2.plan p2.extras 69 76 :=
  window (g:=prices) (by decide +kernel)
private theorem part77 : Window p2.plan p2.extras 77 84 :=
  window (g:=prices) (by decide +kernel)
private theorem part85 : Window p2.plan p2.extras 85 92 :=
  window (g:=prices) (by decide +kernel)
private theorem part93 : Window p2.plan p2.extras 93 100 :=
  window (g:=prices) (by decide +kernel)

theorem p2_valid : p2.Valid := by
  change p2.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join part45 (join part53 part61)) (join (join part69 part77) (join part85 part93)))

end JSP233.Credit19227
