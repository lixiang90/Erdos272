module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source075 : Source :=
  ⟨⟨54,163,27,8000,1,[
    (.marks 54 1 127 false,282),
    (.marks 54 1 132 false,404),
    (.marks 54 1 137 false,378),
    (.marks 54 1 142 false,462),
    (.marks 54 1 147 false,384),
    (.marks 54 1 152 false,500),
    (.marks 54 1 157 false,458),
    (.marks 54 1 162 false,510),
    (.marks 54 1 163 false,10),
    (.marks 54 2 107 false,123),
    (.marks 54 2 112 false,374),
    (.marks 54 2 117 false,306),
    (.marks 54 2 122 false,372),
    (.marks 54 2 127 false,100),
    (.marks 54 3 97 false,189),
    (.marks 54 3 102 false,317),
    (.marks 54 3 107 false,117),
    (.marks 54 4 87 false,43),
    (.marks 54 4 92 false,288),
    (.marks 54 4 97 false,37),
    (.marks 54 5 82 false,72),
    (.marks 54 5 87 false,162),
    (.marks 54 6 54 false,1),
    (.marks 54 6 57 false,3),
    (.marks 54 6 67 false,3),
    (.marks 54 6 77 false,115),
    (.marks 54 6 82 false,43),
    (.marks 54 7 67 false,2),
    (.marks 54 7 72 false,46),
    (.marks 54 7 77 false,66),
    (.marks 54 8 67 false,4),
    (.marks 54 8 72 false,81),
    (.marks 54 9 62 false,1),
    (.marks 54 9 67 false,24),
    (.marks 54 9 72 false,38),
    (.marks 54 10 62 false,2),
    (.marks 54 10 67 false,47),
    (.marks 54 11 57 false,1),
    (.marks 54 11 62 false,5),
    (.marks 54 11 67 false,34),
    (.marks 54 12 57 false,2),
    (.marks 54 12 62 false,2),
    (.marks 54 12 67 false,27),
    (.marks 54 13 57 false,3),
    (.marks 54 13 62 false,6),
    (.marks 54 13 67 false,16),
    (.marks 54 14 54 false,13),
    (.marks 54 14 57 false,11),
    (.marks 54 14 62 false,17),
    (.marks 54 15 57 false,17),
    (.marks 54 15 62 false,17),
    (.marks 54 16 57 false,14),
    (.marks 54 16 62 false,31),
    (.marks 54 17 62 false,16),
    (.marks 54 18 62 false,8),
    (.marks 54 19 57 false,7),
    (.marks 54 19 62 false,17),
    (.marks 54 20 57 false,6),
    (.marks 54 20 62 false,13),
    (.marks 54 21 57 false,15),
    (.marks 54 22 57 false,4),
    (.overlap 54 27 15 39,8),
    (.overlap 54 29 15 39,158),
    (.overlap 54 31 15 39,18),
    (.overlap 55 30 18 38,270),
    (.overlap 55 32 18 38,190),
    (.overlap 56 31 23 35,166),
    (.overlap 56 33 23 35,18)]⟩,
   [(54,506),(55,482),(56,458),(57,424),(58,475),(59,419),(60,403),(61,345),(62,315),(63,410),(64,378),(65,332),(66,312),(67,248),(68,370),(69,328),(70,304),(71,236),(72,212),(73,306),(74,270),(75,232),(76,196),(77,138),(78,294),(79,218),(80,186),(81,134),(82,94),(83,128),(84,104),(85,42),(88,110),(89,24),(93,116),(94,70),(98,58),(103,47)]⟩

private theorem source075From54 : Window source075.plan source075.extras 54 61 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From62 : Window source075.plan source075.extras 62 69 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From70 : Window source075.plan source075.extras 70 77 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From78 : Window source075.plan source075.extras 78 85 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From86 : Window source075.plan source075.extras 86 93 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From94 : Window source075.plan source075.extras 94 101 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From102 : Window source075.plan source075.extras 102 109 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From110 : Window source075.plan source075.extras 110 117 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From118 : Window source075.plan source075.extras 118 125 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From126 : Window source075.plan source075.extras 126 133 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From134 : Window source075.plan source075.extras 134 141 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From142 : Window source075.plan source075.extras 142 149 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From150 : Window source075.plan source075.extras 150 157 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source075From158 : Window source075.plan source075.extras 158 163 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source075_valid : source075.Valid := by
  change NaturalPopulation20258.Good source075.plan source075.extras
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source075From54 (join source075From62 source075From70)) (join (join source075From78 source075From86) (join source075From94 source075From102))) (join (join source075From110 (join source075From118 source075From126)) (join (join source075From134 source075From142) (join source075From150 source075From158))))

end JSP233.PopulationSources20258
