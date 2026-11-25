module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source038 : Source :=
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
    (.marks 51 7 54 false,2),
    (.marks 51 7 59 false,3),
    (.marks 51 7 69 false,72),
    (.marks 51 7 74 false,23),
    (.marks 51 8 51 false,26),
    (.marks 51 8 54 false,3),
    (.marks 51 8 59 false,3),
    (.marks 51 8 69 false,68),
    (.marks 51 9 64 false,36),
    (.marks 51 9 69 false,17),
    (.marks 51 10 54 false,15),
    (.marks 51 10 59 false,5),
    (.marks 51 10 64 false,39),
    (.marks 51 11 54 false,22),
    (.marks 51 11 59 false,2),
    (.marks 51 11 64 false,30),
    (.marks 51 12 59 false,4),
    (.marks 51 12 64 false,20),
    (.marks 51 13 54 false,1),
    (.marks 51 13 59 false,4),
    (.marks 51 13 64 false,14),
    (.marks 51 14 54 false,20),
    (.marks 51 14 59 false,16),
    (.marks 51 15 59 false,29),
    (.marks 51 16 59 false,41),
    (.marks 51 17 59 false,13),
    (.marks 51 18 59 false,6),
    (.marks 51 19 59 false,8),
    (.overlap 51 25 9 42,140),
    (.overlap 51 27 9 42,90),
    (.overlap 51 29 9 42,168),
    (.overlap 52 26 12 41,156),
    (.overlap 53 26 14 41,36),
    (.overlap 53 28 14 41,216),
    (.overlap 53 30 14 41,92),
    (.overlap 54 30 18 39,160),
    (.overlap 54 32 18 39,24),
    (.overlap 55 31 21 38,276),
    (.overlap 55 33 21 38,184)]⟩,
   [(51,446),(52,448),(53,398),(54,380),(55,407),(56,383),(57,349),(58,321),(59,265),(60,377),(61,319),(62,289),(63,255),(64,223),(65,314),(66,294),(67,230),(68,198),(69,156),(70,289),(71,221),(72,197),(73,127),(74,91),(75,210),(76,174),(77,116),(78,92),(79,16),(80,172),(81,120),(82,80),(85,96),(86,54),(90,70),(95,32)]⟩

private theorem source038From51 : Window source038.plan source038.extras 51 58 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source038From59 : Window source038.plan source038.extras 59 66 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source038From67 : Window source038.plan source038.extras 67 74 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source038From75 : Window source038.plan source038.extras 75 82 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source038From83 : Window source038.plan source038.extras 83 90 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source038From91 : Window source038.plan source038.extras 91 98 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source038From99 : Window source038.plan source038.extras 99 106 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source038From107 : Window source038.plan source038.extras 107 114 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source038From115 : Window source038.plan source038.extras 115 122 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source038From123 : Window source038.plan source038.extras 123 130 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source038From131 : Window source038.plan source038.extras 131 138 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source038From139 : Window source038.plan source038.extras 139 146 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source038From147 : Window source038.plan source038.extras 147 152 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source038_valid : source038.Valid := by
  change NaturalPopulation20258.Good source038.plan source038.extras
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source038From51 (join source038From59 source038From67)) (join source038From75 (join source038From83 source038From91))) (join (join source038From99 (join source038From107 source038From115)) (join (join source038From123 source038From131) (join source038From139 source038From147))))

end JSP233.PopulationSources20258
