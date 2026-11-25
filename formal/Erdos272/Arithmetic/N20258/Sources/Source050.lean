module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source050 : Source :=
  ⟨⟨52,163,28,8000,1,[
    (.marks 52 1 120 false,19),
    (.marks 52 1 125 false,120),
    (.marks 52 1 130 false,446),
    (.marks 52 1 135 false,346),
    (.marks 52 1 140 false,452),
    (.marks 52 1 145 false,418),
    (.marks 52 1 150 false,488),
    (.marks 52 1 155 false,392),
    (.marks 52 1 160 false,528),
    (.marks 52 1 163 false,224),
    (.marks 52 2 105 false,34),
    (.marks 52 2 110 false,356),
    (.marks 52 2 115 false,336),
    (.marks 52 2 120 false,343),
    (.marks 52 2 125 false,212),
    (.marks 52 3 95 false,144),
    (.marks 52 3 100 false,268),
    (.marks 52 3 105 false,216),
    (.marks 52 4 90 false,270),
    (.marks 52 4 95 false,98),
    (.marks 52 5 80 false,25),
    (.marks 52 5 85 false,211),
    (.marks 52 6 65 false,5),
    (.marks 52 6 75 false,42),
    (.marks 52 6 80 false,116),
    (.marks 52 7 65 false,5),
    (.marks 52 7 70 false,1),
    (.marks 52 7 75 false,111),
    (.marks 52 8 52 false,12),
    (.marks 52 8 65 false,5),
    (.marks 52 8 70 false,59),
    (.marks 52 8 75 false,23),
    (.marks 52 9 55 false,6),
    (.marks 52 9 65 false,2),
    (.marks 52 9 70 false,60),
    (.marks 52 10 55 false,26),
    (.marks 52 10 65 false,11),
    (.marks 52 10 70 false,38),
    (.marks 52 11 55 false,23),
    (.marks 52 11 60 false,3),
    (.marks 52 11 65 false,36),
    (.marks 52 12 55 false,1),
    (.marks 52 12 60 false,2),
    (.marks 52 12 65 false,28),
    (.marks 52 13 55 false,21),
    (.marks 52 13 60 false,4),
    (.marks 52 13 65 false,19),
    (.marks 52 14 60 false,2),
    (.marks 52 14 65 false,16),
    (.marks 52 15 60 false,23),
    (.marks 52 15 65 false,11),
    (.marks 52 16 60 false,28),
    (.marks 52 16 65 false,7),
    (.marks 52 17 60 false,2),
    (.marks 52 17 65 false,15),
    (.marks 52 18 60 false,7),
    (.marks 52 19 60 false,40),
    (.marks 52 20 60 false,13),
    (.overlap 52 25 9 43,138),
    (.overlap 53 24 12 42,48),
    (.overlap 53 26 12 42,540),
    (.overlap 53 28 12 42,64),
    (.overlap 54 28 14 42,152),
    (.overlap 54 30 14 42,100),
    (.overlap 55 27 17 41,102),
    (.overlap 55 29 17 41,320),
    (.overlap 56 31 21 39,178),
    (.overlap 57 31 25 37,46),
    (.overlap 57 33 25 37,288),
    (.overlap 57 35 25 37,50)]⟩,
   [(52,472),(53,434),(54,416),(55,378),(56,430),(57,396),(58,368),(59,312),(60,296),(61,358),(62,328),(63,294),(64,262),(65,216),(66,349),(67,285),(68,253),(69,211),(70,187),(71,275),(72,251),(73,181),(74,145),(75,107),(76,246),(77,188),(78,164),(79,88),(80,56),(81,144),(82,104),(83,24),(86,107),(87,53),(88,13),(91,102),(92,58),(96,94),(101,30)]⟩

private theorem source050From52 : Window source050.plan source050.extras 52 59 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From60 : Window source050.plan source050.extras 60 67 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From68 : Window source050.plan source050.extras 68 75 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From76 : Window source050.plan source050.extras 76 83 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From84 : Window source050.plan source050.extras 84 91 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From92 : Window source050.plan source050.extras 92 99 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From100 : Window source050.plan source050.extras 100 107 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From108 : Window source050.plan source050.extras 108 115 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From116 : Window source050.plan source050.extras 116 123 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From124 : Window source050.plan source050.extras 124 131 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From132 : Window source050.plan source050.extras 132 139 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From140 : Window source050.plan source050.extras 140 147 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From148 : Window source050.plan source050.extras 148 155 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source050From156 : Window source050.plan source050.extras 156 163 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source050_valid : source050.Valid := by
  change NaturalPopulation20258.Good source050.plan source050.extras
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source050From52 (join source050From60 source050From68)) (join (join source050From76 source050From84) (join source050From92 source050From100))) (join (join source050From108 (join source050From116 source050From124)) (join (join source050From132 source050From140) (join source050From148 source050From156))))

end JSP233.PopulationSources20258
