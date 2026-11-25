module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source011 : Source :=
  ⟨⟨48,152,28,7000,100,[
    (.marks 48 1 48 false,1501),
    (.marks 48 1 53 false,901),
    (.marks 48 1 56 false,1901),
    (.marks 48 1 62 false,2601),
    (.marks 48 1 68 false,3201),
    (.marks 48 1 71 false,301),
    (.marks 48 1 74 false,2801),
    (.marks 48 1 80 false,4001),
    (.marks 48 1 86 false,3801),
    (.marks 48 1 89 false,101),
    (.marks 48 1 92 false,3601),
    (.marks 48 1 98 false,4001),
    (.marks 48 1 101 false,1501),
    (.marks 48 1 104 false,2401),
    (.marks 48 1 107 false,2401),
    (.marks 48 1 110 false,3101),
    (.marks 48 1 113 false,1601),
    (.marks 48 1 116 false,10301),
    (.marks 48 1 119 false,18401),
    (.marks 48 1 122 false,24601),
    (.marks 48 1 125 false,19401),
    (.marks 48 1 128 false,27001),
    (.marks 48 1 131 false,21601),
    (.marks 48 1 134 false,24201),
    (.marks 48 1 137 false,24201),
    (.marks 48 1 140 false,27401),
    (.marks 48 1 143 false,23601),
    (.marks 48 1 146 false,26401),
    (.marks 48 1 149 false,25801),
    (.marks 48 1 152 false,29201),
    (.marks 48 2 48 false,2101),
    (.marks 48 2 50 false,335),
    (.marks 48 2 53 false,35),
    (.marks 48 2 56 false,601),
    (.marks 48 2 59 false,1035),
    (.marks 48 2 62 false,601),
    (.marks 48 2 68 false,1401),
    (.marks 48 2 71 false,235),
    (.marks 48 2 74 false,868),
    (.marks 48 2 80 false,1735),
    (.marks 48 2 83 false,1335),
    (.marks 48 2 89 false,301),
    (.marks 48 2 92 false,1268),
    (.marks 48 2 95 false,735),
    (.marks 48 2 98 false,4201),
    (.marks 48 2 101 false,15501),
    (.marks 48 2 104 false,17001),
    (.marks 48 2 107 false,16801),
    (.marks 48 2 110 false,18501),
    (.marks 48 2 113 false,17801),
    (.marks 48 2 116 false,10901),
    (.marks 48 3 50 false,3448),
    (.marks 48 3 53 false,388),
    (.marks 48 3 59 false,618),
    (.marks 48 3 62 false,18),
    (.marks 48 3 65 false,485),
    (.marks 48 3 68 false,641),
    (.marks 48 3 71 false,228),
    (.marks 48 3 74 false,378),
    (.marks 48 3 77 false,508),
    (.marks 48 3 80 false,268),
    (.marks 48 3 83 false,168),
    (.marks 48 3 89 false,13001),
    (.marks 48 3 92 false,11535),
    (.marks 48 3 95 false,14868),
    (.marks 48 3 98 false,11201),
    (.marks 48 4 50 false,1621),
    (.marks 48 4 56 false,801),
    (.marks 48 4 62 false,698),
    (.marks 48 4 65 false,85),
    (.marks 48 4 68 false,172),
    (.marks 48 4 74 false,371),
    (.marks 48 4 80 false,3161),
    (.marks 48 4 83 false,12901),
    (.marks 48 4 86 false,12001),
    (.marks 48 4 89 false,1601),
    (.marks 48 5 53 false,3381),
    (.marks 48 5 56 false,68),
    (.marks 48 5 59 false,338),
    (.marks 48 5 71 false,431),
    (.marks 48 5 74 false,955),
    (.marks 48 5 77 false,11361),
    (.marks 48 5 80 false,6841),
    (.marks 48 6 53 false,9606),
    (.marks 48 6 59 false,11),
    (.marks 48 6 65 false,482),
    (.marks 48 6 71 false,4087),
    (.marks 48 6 74 false,8968),
    (.marks 48 7 65 false,366),
    (.marks 48 7 68 false,2991),
    (.marks 48 7 71 false,6326),
    (.marks 48 8 53 false,3040),
    (.marks 48 8 59 false,338),
    (.marks 48 8 65 false,1399),
    (.marks 48 8 68 false,5401),
    (.marks 48 9 65 false,5119),
    (.marks 48 10 56 false,1535),
    (.marks 48 10 59 false,568),
    (.marks 48 10 62 false,1719),
    (.marks 48 10 65 false,2208),
    (.marks 48 11 56 false,2301),
    (.marks 48 11 59 false,101),
    (.marks 48 11 62 false,2905),
    (.marks 48 12 56 false,101),
    (.marks 48 12 59 false,201),
    (.marks 48 12 62 false,1989),
    (.marks 48 13 56 false,101),
    (.marks 48 13 59 false,301),
    (.marks 48 13 62 false,1348),
    (.marks 48 14 56 false,559),
    (.marks 53 14 56 false,1544),
    (.marks 53 14 59 false,1235),
    (.marks 53 15 59 false,1793),
    (.marks 53 16 59 false,3576),
    (.overlap 48 21 3 45,18601),
    (.overlap 48 22 3 45,10601),
    (.overlap 49 22 5 45,21801),
    (.overlap 49 23 5 45,22601),
    (.overlap 50 23 7 45,3401),
    (.overlap 50 24 7 45,19601),
    (.overlap 51 24 9 45,27001),
    (.overlap 52 24 11 45,8401),
    (.overlap 52 25 11 45,1401),
    (.overlap 52 26 11 45,22001),
    (.overlap 52 27 11 45,16401),
    (.overlap 52 28 11 45,17801),
    (.overlap 53 29 14 44,14601),
    (.overlap 53 30 14 44,21801),
    (.overlap 53 31 14 44,14801),
    (.overlap 54 31 17 43,201),
    (.overlap 54 32 17 43,23601),
    (.overlap 54 33 17 43,501),
    (.overlap 55 33 19 43,18501),
    (.overlap 55 34 19 43,8801),
    (.overlap 56 35 23 41,18001),
    (.overlap 56 36 23 41,13501),
    (.overlap 57 36 26 40,4301),
    (.overlap 57 37 26 40,7801),
    (.overlap 57 38 26 40,9801),
    (.overlap 57 40 26 40,4101)]⟩,
   []⟩

private theorem source011From48 : Window source011.plan source011.extras 48 55 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From56 : Window source011.plan source011.extras 56 63 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From64 : Window source011.plan source011.extras 64 71 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From72 : Window source011.plan source011.extras 72 79 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From80 : Window source011.plan source011.extras 80 87 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From88 : Window source011.plan source011.extras 88 95 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From96 : Window source011.plan source011.extras 96 103 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From104 : Window source011.plan source011.extras 104 111 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From112 : Window source011.plan source011.extras 112 119 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From120 : Window source011.plan source011.extras 120 127 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From128 : Window source011.plan source011.extras 128 135 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From136 : Window source011.plan source011.extras 136 143 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From144 : Window source011.plan source011.extras 144 151 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source011From152 : Window source011.plan source011.extras 152 152 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source011_valid : source011.Valid := by
  change source011.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source011From48 (join source011From56 source011From64)) (join (join source011From72 source011From80) (join source011From88 source011From96))) (join (join source011From104 (join source011From112 source011From120)) (join (join source011From128 source011From136) (join source011From144 source011From152))))

end JSP233.PopulationSources20258
