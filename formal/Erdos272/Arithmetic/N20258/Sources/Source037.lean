module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source037 : Source :=
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
    (.marks 51 6 51 false,1),
    (.marks 51 6 54 false,3),
    (.marks 51 6 69 false,1),
    (.marks 51 6 74 false,135),
    (.marks 51 7 51 false,2),
    (.marks 51 7 59 false,3),
    (.marks 51 7 69 false,72),
    (.marks 51 7 74 false,23),
    (.marks 51 8 59 false,3),
    (.marks 51 8 69 false,68),
    (.marks 51 9 59 false,3),
    (.marks 51 9 64 false,37),
    (.marks 51 9 69 false,17),
    (.marks 51 10 51 false,3),
    (.marks 51 10 59 false,4),
    (.marks 51 10 64 false,38),
    (.marks 51 11 51 false,22),
    (.marks 51 11 59 false,3),
    (.marks 51 11 64 false,30),
    (.marks 51 12 54 false,21),
    (.marks 51 12 59 false,4),
    (.marks 51 12 64 false,20),
    (.marks 51 13 54 false,1),
    (.marks 51 13 59 false,4),
    (.marks 51 13 64 false,14),
    (.marks 51 14 54 false,14),
    (.marks 51 14 59 false,16),
    (.marks 51 15 54 false,17),
    (.marks 51 15 59 false,29),
    (.marks 51 16 54 false,1),
    (.marks 51 16 59 false,18),
    (.marks 51 17 59 false,8),
    (.marks 51 18 54 false,9),
    (.marks 51 18 59 false,19),
    (.marks 51 19 59 false,14),
    (.marks 51 20 59 false,8),
    (.overlap 51 26 12 39,260),
    (.overlap 52 26 14 39,162),
    (.overlap 52 28 14 39,98),
    (.overlap 53 28 18 37,286),
    (.overlap 53 30 18 37,148),
    (.overlap 54 30 22 35,104),
    (.overlap 54 32 22 35,52),
    (.overlap 54 34 22 35,30)]⟩,
   [(51,446),(52,448),(53,398),(54,380),(55,407),(56,383),(57,349),(58,321),(59,265),(60,377),(61,319),(62,289),(63,255),(64,223),(65,314),(66,294),(67,230),(68,198),(69,156),(70,289),(71,221),(72,197),(73,127),(74,91),(75,210),(76,174),(77,116),(78,92),(79,16),(80,172),(81,120),(82,80),(85,96),(86,54),(90,70),(95,32)]⟩

private theorem source037From51 : Window source037.plan source037.extras 51 58 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source037From59 : Window source037.plan source037.extras 59 66 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source037From67 : Window source037.plan source037.extras 67 74 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source037From75 : Window source037.plan source037.extras 75 82 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source037From83 : Window source037.plan source037.extras 83 90 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source037From91 : Window source037.plan source037.extras 91 98 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source037From99 : Window source037.plan source037.extras 99 106 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source037From107 : Window source037.plan source037.extras 107 114 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source037From115 : Window source037.plan source037.extras 115 122 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source037From123 : Window source037.plan source037.extras 123 130 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source037From131 : Window source037.plan source037.extras 131 138 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source037From139 : Window source037.plan source037.extras 139 146 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source037From147 : Window source037.plan source037.extras 147 152 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source037_valid : source037.Valid := by
  change NaturalPopulation20258.Good source037.plan source037.extras
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source037From51 (join source037From59 source037From67)) (join source037From75 (join source037From83 source037From91))) (join (join source037From99 (join source037From107 source037From115)) (join (join source037From123 source037From131) (join source037From139 source037From147))))

end JSP233.PopulationSources20258
