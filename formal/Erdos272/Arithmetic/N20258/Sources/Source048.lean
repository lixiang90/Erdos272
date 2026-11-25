module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source048 : Source :=
  ⟨⟨52,152,26,7000,1,[
    (.marks 52 1 120 false,307),
    (.marks 52 1 125 false,332),
    (.marks 52 1 130 false,446),
    (.marks 52 1 135 false,346),
    (.marks 52 1 140 false,452),
    (.marks 52 1 145 false,418),
    (.marks 52 1 150 false,488),
    (.marks 52 1 152 false,144),
    (.marks 52 2 100 false,89),
    (.marks 52 2 105 false,278),
    (.marks 52 2 110 false,356),
    (.marks 52 2 115 false,336),
    (.marks 52 2 120 false,55),
    (.marks 52 3 90 false,94),
    (.marks 52 3 95 false,300),
    (.marks 52 3 100 false,150),
    (.marks 52 4 85 false,188),
    (.marks 52 4 90 false,130),
    (.marks 52 5 80 false,192),
    (.marks 52 5 85 false,11),
    (.marks 52 6 65 false,7),
    (.marks 52 6 70 false,7),
    (.marks 52 6 75 false,124),
    (.marks 52 7 65 false,5),
    (.marks 52 7 70 false,94),
    (.marks 52 8 65 false,18),
    (.marks 52 8 70 false,54),
    (.marks 52 9 55 false,2),
    (.marks 52 9 65 false,51),
    (.marks 52 10 65 false,39),
    (.marks 52 11 55 false,2),
    (.marks 52 11 60 false,3),
    (.marks 52 11 65 false,28),
    (.marks 52 12 52 false,12),
    (.marks 52 12 55 false,11),
    (.marks 52 12 60 false,14),
    (.marks 52 12 65 false,10),
    (.marks 52 13 55 false,1),
    (.marks 52 13 60 false,18),
    (.marks 52 14 55 false,34),
    (.marks 52 14 60 false,13),
    (.marks 52 15 60 false,29),
    (.marks 52 16 55 false,6),
    (.marks 52 16 60 false,22),
    (.marks 52 17 60 false,10),
    (.marks 52 18 55 false,9),
    (.marks 52 18 60 false,9),
    (.marks 52 19 55 false,14),
    (.marks 52 19 60 false,8),
    (.overlap 52 27 13 39,44),
    (.overlap 52 29 13 39,216),
    (.overlap 53 30 16 38,204),
    (.overlap 53 32 16 38,200),
    (.overlap 54 31 19 37,186),
    (.overlap 55 31 23 35,50),
    (.overlap 55 33 23 35,108)]⟩,
   [(52,472),(53,434),(54,416),(55,378),(56,430),(57,396),(58,368),(59,312),(60,296),(61,358),(62,328),(63,294),(64,262),(65,216),(66,351),(67,287),(68,255),(69,213),(70,189),(71,275),(72,251),(73,181),(74,145),(75,107),(76,195),(77,137),(78,113),(79,37),(80,5),(81,144),(82,104),(83,24),(86,94),(87,40),(91,44),(96,94)]⟩

private theorem source048From52 : Window source048.plan source048.extras 52 59 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source048From60 : Window source048.plan source048.extras 60 67 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source048From68 : Window source048.plan source048.extras 68 75 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source048From76 : Window source048.plan source048.extras 76 83 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source048From84 : Window source048.plan source048.extras 84 91 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source048From92 : Window source048.plan source048.extras 92 99 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source048From100 : Window source048.plan source048.extras 100 107 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source048From108 : Window source048.plan source048.extras 108 115 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source048From116 : Window source048.plan source048.extras 116 123 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source048From124 : Window source048.plan source048.extras 124 131 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source048From132 : Window source048.plan source048.extras 132 139 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source048From140 : Window source048.plan source048.extras 140 147 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source048From148 : Window source048.plan source048.extras 148 152 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source048_valid : source048.Valid := by
  change NaturalPopulation20258.Good source048.plan source048.extras
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source048From52 (join source048From60 source048From68)) (join source048From76 (join source048From84 source048From92))) (join (join source048From100 (join source048From108 source048From116)) (join (join source048From124 source048From132) (join source048From140 source048From148))))

end JSP233.PopulationSources20258
