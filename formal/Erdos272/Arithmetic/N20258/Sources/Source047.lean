module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source047 : Source :=
  ⟨⟨52,141,23,6000,1,[
    (.marks 52 1 110 false,109),
    (.marks 52 1 115 false,336),
    (.marks 52 1 120 false,362),
    (.marks 52 1 125 false,332),
    (.marks 52 1 130 false,446),
    (.marks 52 1 135 false,346),
    (.marks 52 1 140 false,452),
    (.marks 52 1 141 false,50),
    (.marks 52 2 95 false,90),
    (.marks 52 2 100 false,332),
    (.marks 52 2 105 false,278),
    (.marks 52 2 110 false,247),
    (.marks 52 3 85 false,80),
    (.marks 52 3 90 false,264),
    (.marks 52 3 95 false,116),
    (.marks 52 4 80 false,166),
    (.marks 52 4 85 false,102),
    (.marks 52 5 75 false,131),
    (.marks 52 5 80 false,39),
    (.marks 52 6 65 false,7),
    (.marks 52 6 70 false,107),
    (.marks 52 7 52 false,2),
    (.marks 52 7 65 false,75),
    (.marks 52 7 70 false,5),
    (.marks 52 8 55 false,2),
    (.marks 52 8 65 false,56),
    (.marks 52 9 55 false,2),
    (.marks 52 9 60 false,22),
    (.marks 52 9 65 false,18),
    (.marks 52 10 60 false,30),
    (.marks 52 11 55 false,2),
    (.marks 52 11 60 false,23),
    (.marks 52 12 55 false,2),
    (.marks 52 12 60 false,17),
    (.marks 52 13 55 false,5),
    (.marks 52 13 60 false,12),
    (.marks 52 14 52 false,4),
    (.marks 52 14 55 false,22),
    (.marks 52 14 60 false,8),
    (.marks 52 15 55 false,12),
    (.marks 52 15 60 false,8),
    (.marks 52 16 55 false,11),
    (.marks 52 17 55 false,11),
    (.marks 52 18 52 false,5),
    (.marks 52 18 55 false,13),
    (.marks 52 19 52 false,4)]⟩,
   [(52,472),(53,435),(54,417),(55,379),(56,433),(57,399),(58,371),(59,315),(60,299),(61,358),(62,328),(63,294),(64,262),(65,216),(66,351),(67,287),(68,255),(69,213),(70,189),(71,232),(72,208),(73,138),(74,102),(75,64),(76,158),(77,100),(78,76),(81,120),(82,80),(86,54),(91,44)]⟩

private theorem source047From52 : Window source047.plan source047.extras 52 59 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source047From60 : Window source047.plan source047.extras 60 67 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source047From68 : Window source047.plan source047.extras 68 75 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source047From76 : Window source047.plan source047.extras 76 83 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source047From84 : Window source047.plan source047.extras 84 91 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source047From92 : Window source047.plan source047.extras 92 99 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source047From100 : Window source047.plan source047.extras 100 107 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source047From108 : Window source047.plan source047.extras 108 115 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source047From116 : Window source047.plan source047.extras 116 123 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source047From124 : Window source047.plan source047.extras 124 131 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source047From132 : Window source047.plan source047.extras 132 139 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source047From140 : Window source047.plan source047.extras 140 141 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source047_valid : source047.Valid := by
  change NaturalPopulation20258.Good source047.plan source047.extras
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source047From52 (join source047From60 source047From68)) (join source047From76 (join source047From84 source047From92))) (join (join source047From100 (join source047From108 source047From116)) (join source047From124 (join source047From132 source047From140))))

end JSP233.PopulationSources20258
