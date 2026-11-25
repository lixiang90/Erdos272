module

public import Erdos272.Arithmetic.N19227.Prices
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def p1 : Source := ⟨⟨44,100,17,3000,100,[
  (.marks 44 1 44 false,235),
  (.marks 44 1 46 false,1668),
  (.marks 44 1 52 false,1801),
  (.marks 44 1 58 false,4301),
  (.marks 44 1 64 false,1801),
  (.marks 44 1 67 false,701),
  (.marks 44 1 70 false,3101),
  (.marks 44 1 73 false,601),
  (.marks 44 1 76 false,3901),
  (.marks 44 1 79 false,13201),
  (.marks 44 1 82 false,17201),
  (.marks 44 1 85 false,12801),
  (.marks 44 1 88 false,18001),
  (.marks 44 1 91 false,13801),
  (.marks 44 1 94 false,17401),
  (.marks 44 1 97 false,16801),
  (.marks 44 1 100 false,15401),
  (.marks 44 2 44 false,501),
  (.marks 44 2 49 false,168),
  (.marks 44 2 52 false,701),
  (.marks 44 2 55 false,535),
  (.marks 44 2 58 false,968),
  (.marks 44 2 64 false,801),
  (.marks 44 2 67 false,10035),
  (.marks 44 2 70 false,10301),
  (.marks 44 2 73 false,12401),
  (.marks 44 2 76 false,9301),
  (.marks 44 3 49 false,685),
  (.marks 44 3 55 false,568),
  (.marks 44 3 58 false,535),
  (.marks 44 3 61 false,10401),
  (.marks 44 3 64 false,8601),
  (.marks 44 3 67 false,868),
  (.marks 44 4 44 false,175),
  (.marks 44 4 46 false,68),
  (.marks 44 4 49 false,151),
  (.marks 44 4 52 false,301),
  (.marks 44 4 55 false,5581),
  (.marks 44 4 58 false,6001),
  (.marks 44 5 44 false,61),
  (.marks 44 5 49 false,468),
  (.marks 44 5 52 false,4135),
  (.marks 44 5 55 false,2921),
  (.marks 44 6 44 false,92),
  (.marks 44 6 46 false,411),
  (.marks 44 6 49 false,2535),
  (.marks 44 6 52 false,1868),
  (.marks 44 7 44 false,44),
  (.marks 44 7 46 false,34),
  (.marks 44 7 49 false,3001),
  (.marks 44 8 44 false,79),
  (.marks 44 8 46 false,471),
  (.marks 44 8 49 false,1401),
  (.marks 44 9 44 false,164),
  (.marks 44 9 46 false,1077),
  (.marks 44 10 46 false,596),
  (.marks 44 11 44 false,161),
  (.marks 44 11 46 false,1487),
  (.marks 44 12 44 false,701)]⟩,[]⟩

private theorem part44 : Window p1.plan p1.extras 44 51 :=
  window (g:=prices) (by decide +kernel)
private theorem part52 : Window p1.plan p1.extras 52 59 :=
  window (g:=prices) (by decide +kernel)
private theorem part60 : Window p1.plan p1.extras 60 67 :=
  window (g:=prices) (by decide +kernel)
private theorem part68 : Window p1.plan p1.extras 68 75 :=
  window (g:=prices) (by decide +kernel)
private theorem part76 : Window p1.plan p1.extras 76 83 :=
  window (g:=prices) (by decide +kernel)
private theorem part84 : Window p1.plan p1.extras 84 91 :=
  window (g:=prices) (by decide +kernel)
private theorem part92 : Window p1.plan p1.extras 92 99 :=
  window (g:=prices) (by decide +kernel)
private theorem part100 : Window p1.plan p1.extras 100 100 :=
  window (g:=prices) (by decide +kernel)

theorem p1_valid : p1.Valid := by
  change p1.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join part44 part52) (join part60 part68)) (join (join part76 part84) (join part92 part100)))

end JSP233.Credit19227
