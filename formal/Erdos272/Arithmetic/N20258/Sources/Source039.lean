module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source039 : Source :=
  ⟨⟨51,152,26,7000,1,[
    (.marks 51 1 119 false,223),
    (.marks 51 1 124 false,404),
    (.marks 51 1 129 false,354),
    (.marks 51 1 134 false,410),
    (.marks 51 1 139 false,426),
    (.marks 51 1 144 false,436),
    (.marks 51 1 149 false,412),
    (.marks 51 1 152 false,292),
    (.marks 51 2 99 false,10),
    (.marks 51 2 104 false,324),
    (.marks 51 2 109 false,338),
    (.marks 51 2 114 false,350),
    (.marks 51 2 119 false,87),
    (.marks 51 3 89 false,73),
    (.marks 51 3 94 false,250),
    (.marks 51 3 99 false,225),
    (.marks 51 4 84 false,166),
    (.marks 51 4 89 false,148),
    (.marks 51 5 79 false,188),
    (.marks 51 5 84 false,16),
    (.marks 51 6 54 false,3),
    (.marks 51 6 69 false,1),
    (.marks 51 6 74 false,135),
    (.marks 51 7 51 false,26),
    (.marks 51 7 54 false,4),
    (.marks 51 7 59 false,3),
    (.marks 51 7 69 false,72),
    (.marks 51 7 74 false,23),
    (.marks 51 8 54 false,13),
    (.marks 51 8 59 false,3),
    (.marks 51 8 69 false,68),
    (.marks 51 9 54 false,1),
    (.marks 51 9 59 false,2),
    (.marks 51 9 64 false,37),
    (.marks 51 9 69 false,17),
    (.marks 51 10 54 false,24),
    (.marks 51 10 59 false,3),
    (.marks 51 10 64 false,38),
    (.marks 51 11 54 false,1),
    (.marks 51 11 59 false,2),
    (.marks 51 11 64 false,30),
    (.marks 51 12 54 false,21),
    (.marks 51 12 59 false,4),
    (.marks 51 12 64 false,20),
    (.marks 51 13 59 false,4),
    (.marks 51 13 64 false,14),
    (.marks 51 14 59 false,34),
    (.marks 51 15 59 false,29),
    (.marks 51 16 59 false,31),
    (.marks 51 17 59 false,13),
    (.marks 51 18 59 false,4),
    (.overlap 51 26 8 43,332),
    (.overlap 51 28 8 43,58),
    (.overlap 52 28 10 43,156),
    (.overlap 53 27 13 42,90),
    (.overlap 53 29 13 42,165),
    (.overlap 54 28 16 41,2),
    (.overlap 54 30 16 41,252),
    (.overlap 54 32 16 41,19),
    (.overlap 55 29 19 40,3),
    (.overlap 55 31 19 40,397),
    (.overlap 55 33 19 40,60),
    (.overlap 56 32 22 39,20),
    (.overlap 56 34 22 39,144)]⟩,
   [(51,446),(52,448),(53,398),(54,380),(55,407),(56,383),(57,349),(58,321),(59,265),(60,377),(61,319),(62,289),(63,255),(64,223),(65,314),(66,294),(67,230),(68,198),(69,156),(70,289),(71,221),(72,197),(73,127),(74,91),(75,210),(76,174),(77,116),(78,92),(79,16),(80,172),(81,120),(82,80),(85,96),(86,54),(90,70),(95,32)]⟩

private theorem source039From51 : Window source039.plan source039.extras 51 58 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source039From59 : Window source039.plan source039.extras 59 66 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source039From67 : Window source039.plan source039.extras 67 74 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source039From75 : Window source039.plan source039.extras 75 82 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source039From83 : Window source039.plan source039.extras 83 90 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source039From91 : Window source039.plan source039.extras 91 98 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source039From99 : Window source039.plan source039.extras 99 106 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source039From107 : Window source039.plan source039.extras 107 114 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source039From115 : Window source039.plan source039.extras 115 122 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source039From123 : Window source039.plan source039.extras 123 130 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source039From131 : Window source039.plan source039.extras 131 138 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source039From139 : Window source039.plan source039.extras 139 146 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source039From147 : Window source039.plan source039.extras 147 152 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source039_valid : source039.Valid := by
  change NaturalPopulation20258.Good source039.plan source039.extras
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source039From51 (join source039From59 source039From67)) (join source039From75 (join source039From83 source039From91))) (join (join source039From99 (join source039From107 source039From115)) (join (join source039From123 source039From131) (join source039From139 source039From147))))

end JSP233.PopulationSources20258
