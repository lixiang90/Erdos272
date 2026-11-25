module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source036 : Source :=
  ⟨⟨51,141,24,6000,1,[
    (.marks 51 1 109 false,63),
    (.marks 51 1 114 false,350),
    (.marks 51 1 119 false,310),
    (.marks 51 1 124 false,404),
    (.marks 51 1 129 false,354),
    (.marks 51 1 134 false,410),
    (.marks 51 1 139 false,426),
    (.marks 51 1 141 false,140),
    (.marks 51 2 94 false,77),
    (.marks 51 2 99 false,266),
    (.marks 51 2 104 false,324),
    (.marks 51 2 109 false,275),
    (.marks 51 3 84 false,49),
    (.marks 51 3 89 false,274),
    (.marks 51 3 94 false,142),
    (.marks 51 4 79 false,104),
    (.marks 51 4 84 false,160),
    (.marks 51 5 74 false,75),
    (.marks 51 5 79 false,96),
    (.marks 51 6 51 false,1),
    (.marks 51 6 54 false,3),
    (.marks 51 6 69 false,112),
    (.marks 51 7 51 false,2),
    (.marks 51 7 59 false,4),
    (.marks 51 7 64 false,40),
    (.marks 51 7 69 false,37),
    (.marks 51 8 59 false,3),
    (.marks 51 8 64 false,55),
    (.marks 51 9 59 false,3),
    (.marks 51 9 64 false,42),
    (.marks 51 10 51 false,3),
    (.marks 51 10 59 false,32),
    (.marks 51 11 51 false,2),
    (.marks 51 11 59 false,25),
    (.marks 51 12 54 false,1),
    (.marks 51 12 59 false,18),
    (.marks 51 13 51 false,8),
    (.marks 51 13 54 false,5),
    (.marks 51 13 59 false,12),
    (.marks 51 14 54 false,16),
    (.marks 51 14 59 false,11),
    (.marks 51 15 59 false,17),
    (.marks 51 16 59 false,7),
    (.marks 51 17 54 false,20),
    (.marks 51 17 59 false,4),
    (.marks 51 18 54 false,8),
    (.marks 51 19 51 false,2),
    (.marks 51 19 54 false,14),
    (.marks 51 20 51 false,9),
    (.marks 51 21 51 false,3)]⟩,
   [(51,446),(52,448),(53,398),(54,380),(55,407),(56,383),(57,349),(58,321),(59,265),(60,379),(61,321),(62,291),(63,257),(64,225),(65,314),(66,294),(67,230),(68,198),(69,156),(70,280),(71,212),(72,188),(73,118),(74,82),(75,118),(76,82),(77,24),(80,92),(81,40),(85,42),(90,70)]⟩

private theorem source036From51 : Window source036.plan source036.extras 51 58 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source036From59 : Window source036.plan source036.extras 59 66 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source036From67 : Window source036.plan source036.extras 67 74 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source036From75 : Window source036.plan source036.extras 75 82 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source036From83 : Window source036.plan source036.extras 83 90 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source036From91 : Window source036.plan source036.extras 91 98 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source036From99 : Window source036.plan source036.extras 99 106 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source036From107 : Window source036.plan source036.extras 107 114 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source036From115 : Window source036.plan source036.extras 115 122 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source036From123 : Window source036.plan source036.extras 123 130 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source036From131 : Window source036.plan source036.extras 131 138 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source036From139 : Window source036.plan source036.extras 139 141 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source036_valid : source036.Valid := by
  change NaturalPopulation20258.Good source036.plan source036.extras
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source036From51 (join source036From59 source036From67)) (join source036From75 (join source036From83 source036From91))) (join (join source036From99 (join source036From107 source036From115)) (join source036From123 (join source036From131 source036From139))))

end JSP233.PopulationSources20258
