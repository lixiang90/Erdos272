module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source060 : Source :=
  ⟨⟨53,163,28,8000,1,[
    (.marks 53 1 126 false,232),
    (.marks 53 1 131 false,362),
    (.marks 53 1 136 false,440),
    (.marks 53 1 141 false,388),
    (.marks 53 1 146 false,430),
    (.marks 53 1 151 false,478),
    (.marks 53 1 156 false,474),
    (.marks 53 1 161 false,428),
    (.marks 53 1 163 false,170),
    (.marks 53 2 106 false,103),
    (.marks 53 2 111 false,300),
    (.marks 53 2 116 false,358),
    (.marks 53 2 121 false,352),
    (.marks 53 2 126 false,164),
    (.marks 53 3 96 false,151),
    (.marks 53 3 101 false,327),
    (.marks 53 3 106 false,149),
    (.marks 53 4 86 false,37),
    (.marks 53 4 91 false,242),
    (.marks 53 4 96 false,87),
    (.marks 53 5 81 false,51),
    (.marks 53 5 86 false,186),
    (.marks 53 6 53 false,1),
    (.marks 53 6 71 false,3),
    (.marks 53 6 76 false,78),
    (.marks 53 6 81 false,80),
    (.marks 53 7 61 false,4),
    (.marks 53 7 71 false,12),
    (.marks 53 7 76 false,100),
    (.marks 53 8 61 false,3),
    (.marks 53 8 66 false,2),
    (.marks 53 8 71 false,82),
    (.marks 53 9 53 false,27),
    (.marks 53 9 61 false,4),
    (.marks 53 9 66 false,4),
    (.marks 53 9 71 false,59),
    (.marks 53 10 61 false,3),
    (.marks 53 10 66 false,37),
    (.marks 53 10 71 false,9),
    (.marks 53 11 56 false,21),
    (.marks 53 11 61 false,4),
    (.marks 53 11 66 false,36),
    (.marks 53 12 56 false,2),
    (.marks 53 12 61 false,3),
    (.marks 53 12 66 false,26),
    (.marks 53 13 56 false,22),
    (.marks 53 13 61 false,2),
    (.marks 53 13 66 false,20),
    (.marks 53 14 61 false,4),
    (.marks 53 14 66 false,14),
    (.marks 53 15 56 false,21),
    (.marks 53 15 61 false,14),
    (.marks 53 15 66 false,9),
    (.marks 53 16 61 false,25),
    (.marks 53 17 61 false,16),
    (.marks 53 18 61 false,35),
    (.marks 53 19 61 false,12),
    (.marks 53 20 61 false,13),
    (.overlap 53 26 10 43,168),
    (.overlap 53 28 10 43,196),
    (.overlap 54 27 13 42,252),
    (.overlap 55 28 16 41,44),
    (.overlap 55 30 16 41,272),
    (.overlap 56 29 19 40,144),
    (.overlap 56 31 19 40,16),
    (.overlap 57 31 23 38,458),
    (.overlap 57 35 23 38,14),
    (.overlap 57 37 23 38,60)]⟩,
   [(53,472),(54,481),(55,443),(56,419),(57,451),(58,423),(59,367),(60,351),(61,293),(62,399),(63,365),(64,333),(65,287),(66,267),(67,347),(68,315),(69,273),(70,249),(71,181),(72,321),(73,251),(74,215),(75,177),(76,141),(77,260),(78,236),(79,160),(80,128),(81,76),(82,166),(83,86),(84,62),(87,126),(88,86),(92,104),(93,46),(97,42),(102,99)]⟩

private theorem source060From53 : Window source060.plan source060.extras 53 60 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From61 : Window source060.plan source060.extras 61 68 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From69 : Window source060.plan source060.extras 69 76 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From77 : Window source060.plan source060.extras 77 84 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From85 : Window source060.plan source060.extras 85 92 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From93 : Window source060.plan source060.extras 93 100 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From101 : Window source060.plan source060.extras 101 108 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From109 : Window source060.plan source060.extras 109 116 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From117 : Window source060.plan source060.extras 117 124 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From125 : Window source060.plan source060.extras 125 132 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From133 : Window source060.plan source060.extras 133 140 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From141 : Window source060.plan source060.extras 141 148 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From149 : Window source060.plan source060.extras 149 156 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source060From157 : Window source060.plan source060.extras 157 163 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source060_valid : source060.Valid := by
  change NaturalPopulation20258.Good source060.plan source060.extras
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source060From53 (join source060From61 source060From69)) (join (join source060From77 source060From85) (join source060From93 source060From101))) (join (join source060From109 (join source060From117 source060From125)) (join (join source060From133 source060From141) (join source060From149 source060From157))))

end JSP233.PopulationSources20258
