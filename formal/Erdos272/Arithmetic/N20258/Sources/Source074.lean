module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source074 : Source :=
  ⟨⟨54,152,25,7000,1,[
    (.marks 54 1 117 false,28),
    (.marks 54 1 122 false,372),
    (.marks 54 1 127 false,382),
    (.marks 54 1 132 false,404),
    (.marks 54 1 137 false,378),
    (.marks 54 1 142 false,462),
    (.marks 54 1 147 false,384),
    (.marks 54 1 152 false,478),
    (.marks 54 2 102 false,170),
    (.marks 54 2 107 false,286),
    (.marks 54 2 112 false,374),
    (.marks 54 2 117 false,278),
    (.marks 54 3 92 false,143),
    (.marks 54 3 97 false,296),
    (.marks 54 3 102 false,100),
    (.marks 54 4 87 false,243),
    (.marks 54 4 92 false,75),
    (.marks 54 5 82 false,200),
    (.marks 54 6 54 false,1),
    (.marks 54 6 57 false,3),
    (.marks 54 6 67 false,4),
    (.marks 54 6 72 false,77),
    (.marks 54 6 77 false,56),
    (.marks 54 7 67 false,9),
    (.marks 54 7 72 false,87),
    (.marks 54 8 67 false,70),
    (.marks 54 9 62 false,1),
    (.marks 54 9 67 false,51),
    (.marks 54 10 62 false,17),
    (.marks 54 10 67 false,22),
    (.marks 54 11 57 false,1),
    (.marks 54 11 62 false,31),
    (.marks 54 12 57 false,2),
    (.marks 54 12 62 false,22),
    (.marks 54 13 57 false,3),
    (.marks 54 13 62 false,16),
    (.marks 54 14 54 false,4),
    (.marks 54 14 57 false,11),
    (.marks 54 14 62 false,12),
    (.marks 54 15 54 false,1),
    (.marks 54 15 57 false,16),
    (.marks 54 15 62 false,13),
    (.marks 54 16 62 false,18),
    (.marks 54 17 57 false,6),
    (.marks 54 17 62 false,3),
    (.marks 54 18 54 false,1),
    (.marks 54 18 57 false,19),
    (.marks 54 19 57 false,13),
    (.marks 54 20 54 false,4),
    (.marks 54 20 57 false,9),
    (.marks 54 21 54 false,6)]⟩,
   [(54,506),(55,482),(56,458),(57,424),(58,475),(59,419),(60,403),(61,345),(62,315),(63,410),(64,378),(65,332),(66,312),(67,248),(68,371),(69,329),(70,305),(71,237),(72,213),(73,306),(74,270),(75,232),(76,196),(77,138),(78,170),(79,94),(80,62),(81,10),(83,90),(84,66),(85,4),(88,110),(89,24),(93,46),(98,58)]⟩

private theorem source074From54 : Window source074.plan source074.extras 54 61 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source074From62 : Window source074.plan source074.extras 62 69 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source074From70 : Window source074.plan source074.extras 70 77 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source074From78 : Window source074.plan source074.extras 78 85 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source074From86 : Window source074.plan source074.extras 86 93 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source074From94 : Window source074.plan source074.extras 94 101 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source074From102 : Window source074.plan source074.extras 102 109 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source074From110 : Window source074.plan source074.extras 110 117 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source074From118 : Window source074.plan source074.extras 118 125 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source074From126 : Window source074.plan source074.extras 126 133 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source074From134 : Window source074.plan source074.extras 134 141 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source074From142 : Window source074.plan source074.extras 142 149 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source074From150 : Window source074.plan source074.extras 150 152 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source074_valid : source074.Valid := by
  change NaturalPopulation20258.Good source074.plan source074.extras
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source074From54 (join source074From62 source074From70)) (join source074From78 (join source074From86 source074From94))) (join (join source074From102 (join source074From110 source074From118)) (join (join source074From126 source074From134) (join source074From142 source074From150))))

end JSP233.PopulationSources20258
