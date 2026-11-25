module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source071 : Source :=
  ⟨⟨53,182,32,10000,1,[
    (.marks 53 1 126 false,40),
    (.marks 53 1 136 false,128),
    (.marks 53 1 141 false,254),
    (.marks 53 1 146 false,430),
    (.marks 53 1 151 false,478),
    (.marks 53 1 156 false,474),
    (.marks 53 1 161 false,428),
    (.marks 53 1 166 false,564),
    (.marks 53 1 171 false,456),
    (.marks 53 1 176 false,538),
    (.marks 53 1 181 false,562),
    (.marks 53 1 182 false,50),
    (.marks 53 2 106 false,6),
    (.marks 53 2 116 false,89),
    (.marks 53 2 121 false,352),
    (.marks 53 2 126 false,347),
    (.marks 53 2 131 false,371),
    (.marks 53 2 136 false,312),
    (.marks 53 2 141 false,134),
    (.marks 53 3 101 false,32),
    (.marks 53 3 106 false,192),
    (.marks 53 3 111 false,308),
    (.marks 53 3 116 false,262),
    (.marks 53 4 96 false,161),
    (.marks 53 4 101 false,251),
    (.marks 53 4 106 false,54),
    (.marks 53 5 86 false,13),
    (.marks 53 5 91 false,235),
    (.marks 53 5 96 false,87),
    (.marks 53 6 56 false,16),
    (.marks 53 6 71 false,3),
    (.marks 53 6 76 false,2),
    (.marks 53 6 81 false,3),
    (.marks 53 6 86 false,182),
    (.marks 53 6 91 false,18),
    (.marks 53 7 61 false,5),
    (.marks 53 7 71 false,3),
    (.marks 53 7 76 false,3),
    (.marks 53 7 81 false,119),
    (.marks 53 7 86 false,23),
    (.marks 53 8 56 false,28),
    (.marks 53 8 61 false,5),
    (.marks 53 8 66 false,2),
    (.marks 53 8 71 false,3),
    (.marks 53 8 76 false,38),
    (.marks 53 8 81 false,69),
    (.marks 53 9 56 false,19),
    (.marks 53 9 61 false,1),
    (.marks 53 9 66 false,4),
    (.marks 53 9 71 false,3),
    (.marks 53 9 76 false,79),
    (.marks 53 10 61 false,4),
    (.marks 53 10 66 false,2),
    (.marks 53 10 71 false,6),
    (.marks 53 10 76 false,56),
    (.marks 53 11 61 false,25),
    (.marks 53 11 66 false,3),
    (.marks 53 11 71 false,48),
    (.marks 53 12 61 false,3),
    (.marks 53 12 66 false,2),
    (.marks 53 12 71 false,37),
    (.marks 53 13 61 false,24),
    (.marks 53 13 66 false,4),
    (.marks 53 13 71 false,27),
    (.marks 53 14 61 false,2),
    (.marks 53 14 66 false,1),
    (.marks 53 14 71 false,22),
    (.marks 53 15 61 false,23),
    (.marks 53 15 66 false,4),
    (.marks 53 15 71 false,15),
    (.marks 53 16 61 false,15),
    (.marks 53 16 66 false,14),
    (.marks 53 17 66 false,29),
    (.marks 53 18 61 false,5),
    (.marks 53 18 66 false,26),
    (.marks 53 19 66 false,11),
    (.marks 53 20 61 false,12),
    (.marks 53 20 66 false,9),
    (.marks 53 21 66 false,18),
    (.marks 53 22 61 false,16),
    (.marks 53 22 66 false,19),
    (.overlap 53 22 6 47,334),
    (.overlap 53 24 6 47,306),
    (.overlap 54 24 8 47,354),
    (.overlap 54 26 8 47,76),
    (.overlap 55 23 11 46,310),
    (.overlap 55 25 11 46,196),
    (.overlap 56 25 13 46,68),
    (.overlap 56 27 13 46,324),
    (.overlap 57 26 16 45,452),
    (.overlap 57 28 16 45,240),
    (.overlap 58 29 19 44,144),
    (.overlap 58 31 19 44,176),
    (.overlap 58 33 19 44,2),
    (.overlap 59 30 22 43,280),
    (.overlap 59 32 22 43,354),
    (.overlap 59 34 22 43,92),
    (.overlap 60 34 26 41,124),
    (.overlap 60 36 26 41,80),
    (.overlap 61 35 31 38,254),
    (.overlap 61 37 31 38,274)]⟩,
   [(53,472),(54,454),(55,416),(56,392),(57,420),(58,392),(59,336),(60,320),(61,262),(62,368),(63,334),(64,302),(65,256),(66,236),(67,316),(68,284),(69,242),(70,218),(71,150),(72,290),(73,220),(74,184),(75,146),(76,110),(77,229),(78,205),(79,129),(80,97),(81,45),(82,196),(83,116),(84,92),(85,30),(87,150),(88,110),(89,24),(92,139),(93,81),(94,35),(97,86),(98,44),(102,99),(112,8)]⟩

private theorem source071From53 : Window source071.plan source071.extras 53 60 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From61 : Window source071.plan source071.extras 61 68 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From69 : Window source071.plan source071.extras 69 76 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From77 : Window source071.plan source071.extras 77 84 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From85 : Window source071.plan source071.extras 85 92 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From93 : Window source071.plan source071.extras 93 100 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From101 : Window source071.plan source071.extras 101 108 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From109 : Window source071.plan source071.extras 109 116 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From117 : Window source071.plan source071.extras 117 124 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From125 : Window source071.plan source071.extras 125 132 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From133 : Window source071.plan source071.extras 133 140 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From141 : Window source071.plan source071.extras 141 148 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From149 : Window source071.plan source071.extras 149 156 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From157 : Window source071.plan source071.extras 157 164 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From165 : Window source071.plan source071.extras 165 172 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From173 : Window source071.plan source071.extras 173 180 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source071From181 : Window source071.plan source071.extras 181 182 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source071_valid : source071.Valid := by
  change NaturalPopulation20258.Good source071.plan source071.extras
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join (join source071From53 source071From61) (join source071From69 source071From77)) (join (join source071From85 source071From93) (join source071From101 source071From109))) (join (join (join source071From117 source071From125) (join source071From133 source071From141)) (join (join source071From149 source071From157) (join source071From165 (join source071From173 source071From181)))))

end JSP233.PopulationSources20258
