module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source058 : Source :=
  ⟨⟨53,152,25,7000,1,[
    (.marks 53 1 121 false,336),
    (.marks 53 1 126 false,396),
    (.marks 53 1 131 false,362),
    (.marks 53 1 136 false,440),
    (.marks 53 1 141 false,388),
    (.marks 53 1 146 false,430),
    (.marks 53 1 151 false,478),
    (.marks 53 1 152 false,72),
    (.marks 53 2 101 false,86),
    (.marks 53 2 106 false,350),
    (.marks 53 2 111 false,300),
    (.marks 53 2 116 false,358),
    (.marks 53 2 121 false,16),
    (.marks 53 3 91 false,117),
    (.marks 53 3 96 false,284),
    (.marks 53 3 101 false,142),
    (.marks 53 4 86 false,237),
    (.marks 53 4 91 false,79),
    (.marks 53 5 81 false,203),
    (.marks 53 6 53 false,1),
    (.marks 53 6 71 false,46),
    (.marks 53 6 76 false,90),
    (.marks 53 7 61 false,4),
    (.marks 53 7 71 false,94),
    (.marks 53 8 61 false,3),
    (.marks 53 8 66 false,45),
    (.marks 53 8 71 false,25),
    (.marks 53 9 53 false,1),
    (.marks 53 9 61 false,4),
    (.marks 53 9 66 false,52),
    (.marks 53 10 53 false,4),
    (.marks 53 10 61 false,3),
    (.marks 53 10 66 false,37),
    (.marks 53 11 53 false,1),
    (.marks 53 11 61 false,20),
    (.marks 53 11 66 false,12),
    (.marks 53 12 53 false,1),
    (.marks 53 12 56 false,2),
    (.marks 53 12 61 false,22),
    (.marks 53 13 56 false,2),
    (.marks 53 13 61 false,17),
    (.marks 53 14 53 false,20),
    (.marks 53 14 56 false,14),
    (.marks 53 14 61 false,13),
    (.marks 53 15 56 false,11),
    (.marks 53 15 61 false,18),
    (.marks 53 16 56 false,7),
    (.marks 53 16 61 false,21),
    (.marks 53 17 61 false,10),
    (.marks 53 18 56 false,11),
    (.marks 53 18 61 false,7),
    (.marks 53 19 56 false,22),
    (.overlap 53 29 15 38,22),
    (.overlap 53 31 15 38,184),
    (.overlap 53 33 15 38,198),
    (.overlap 54 30 18 37,54),
    (.overlap 54 32 18 37,132),
    (.overlap 55 32 22 35,158)]⟩,
   [(53,472),(54,481),(55,443),(56,419),(57,451),(58,423),(59,367),(60,351),(61,293),(62,399),(63,365),(64,333),(65,287),(66,267),(67,347),(68,315),(69,273),(70,249),(71,181),(72,321),(73,251),(74,215),(75,177),(76,141),(77,173),(78,149),(79,73),(80,41),(82,152),(83,72),(84,48),(87,126),(88,86),(92,58),(97,42)]⟩

private theorem source058From53 : Window source058.plan source058.extras 53 60 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source058From61 : Window source058.plan source058.extras 61 68 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source058From69 : Window source058.plan source058.extras 69 76 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source058From77 : Window source058.plan source058.extras 77 84 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source058From85 : Window source058.plan source058.extras 85 92 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source058From93 : Window source058.plan source058.extras 93 100 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source058From101 : Window source058.plan source058.extras 101 108 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source058From109 : Window source058.plan source058.extras 109 116 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source058From117 : Window source058.plan source058.extras 117 124 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source058From125 : Window source058.plan source058.extras 125 132 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source058From133 : Window source058.plan source058.extras 133 140 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source058From141 : Window source058.plan source058.extras 141 148 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source058From149 : Window source058.plan source058.extras 149 152 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source058_valid : source058.Valid := by
  change NaturalPopulation20258.Good source058.plan source058.extras
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source058From53 (join source058From61 source058From69)) (join source058From77 (join source058From85 source058From93))) (join (join source058From101 (join source058From109 source058From117)) (join (join source058From125 source058From133) (join source058From141 source058From149))))

end JSP233.PopulationSources20258
