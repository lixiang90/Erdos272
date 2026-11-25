module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source012 : Source :=
  ⟨⟨48,152,28,7000,100,[
    (.marks 48 1 48 false,3601),
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
    (.marks 48 2 50 false,3801),
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
    (.marks 48 3 50 false,1601),
    (.marks 48 3 53 false,818),
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
    (.marks 48 4 53 false,2691),
    (.marks 48 4 56 false,801),
    (.marks 48 4 62 false,676),
    (.marks 48 4 65 false,85),
    (.marks 48 4 68 false,193),
    (.marks 48 4 74 false,371),
    (.marks 48 4 80 false,3161),
    (.marks 48 4 83 false,12901),
    (.marks 48 4 86 false,12001),
    (.marks 48 4 89 false,1601),
    (.marks 48 5 53 false,261),
    (.marks 48 5 56 false,68),
    (.marks 48 5 59 false,360),
    (.marks 48 5 71 false,410),
    (.marks 48 5 74 false,955),
    (.marks 48 5 77 false,11361),
    (.marks 48 5 80 false,6841),
    (.marks 48 6 53 false,7159),
    (.marks 48 6 56 false,60),
    (.marks 48 6 59 false,11),
    (.marks 48 6 65 false,482),
    (.marks 48 6 71 false,4087),
    (.marks 48 6 74 false,8968),
    (.marks 48 7 53 false,3098),
    (.marks 48 7 59 false,59),
    (.marks 48 7 65 false,387),
    (.marks 48 7 68 false,2970),
    (.marks 48 7 71 false,6347),
    (.marks 48 8 56 false,1276),
    (.marks 48 8 59 false,526),
    (.marks 48 8 65 false,1399),
    (.marks 48 8 68 false,5401),
    (.marks 48 9 56 false,201),
    (.marks 48 9 62 false,176),
    (.marks 48 9 65 false,5104),
    (.marks 48 10 56 false,2301),
    (.marks 48 10 59 false,301),
    (.marks 48 10 62 false,1565),
    (.marks 48 10 65 false,2201),
    (.marks 48 11 59 false,101),
    (.marks 48 11 62 false,2905),
    (.marks 48 12 56 false,2301),
    (.marks 48 12 59 false,201),
    (.marks 48 12 62 false,1989),
    (.marks 48 13 59 false,301),
    (.marks 48 13 62 false,1348),
    (.marks 48 14 59 false,848),
    (.marks 53 14 59 false,2489),
    (.marks 53 15 59 false,1243),
    (.marks 53 16 59 false,2026),
    (.overlap 48 21 2 46,18601),
    (.overlap 48 22 2 46,10601),
    (.overlap 49 22 4 46,21801),
    (.overlap 49 23 4 46,21555),
    (.overlap 50 23 6 46,4448),
    (.overlap 50 24 6 46,19601),
    (.overlap 51 24 8 46,26801),
    (.overlap 52 24 11 45,8601),
    (.overlap 52 25 11 45,1401),
    (.overlap 52 26 11 45,22001),
    (.overlap 52 27 11 45,16401),
    (.overlap 52 28 11 45,12755),
    (.overlap 53 28 13 45,5048),
    (.overlap 53 29 13 45,14601),
    (.overlap 53 30 13 45,21801),
    (.overlap 53 31 13 45,10755),
    (.overlap 54 31 15 45,4248),
    (.overlap 54 32 15 45,10155),
    (.overlap 55 32 18 44,13448),
    (.overlap 55 33 18 44,13955),
    (.overlap 56 33 21 43,4001),
    (.overlap 56 34 21 43,9848),
    (.overlap 56 35 21 43,12955),
    (.overlap 56 36 21 43,4701),
    (.overlap 57 36 24 42,13101),
    (.overlap 57 37 24 42,8801),
    (.overlap 57 38 24 42,9601)]⟩,
   []⟩

private theorem source012From48 : Window source012.plan source012.extras 48 55 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From56 : Window source012.plan source012.extras 56 63 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From64 : Window source012.plan source012.extras 64 71 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From72 : Window source012.plan source012.extras 72 79 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From80 : Window source012.plan source012.extras 80 87 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From88 : Window source012.plan source012.extras 88 95 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From96 : Window source012.plan source012.extras 96 103 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From104 : Window source012.plan source012.extras 104 111 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From112 : Window source012.plan source012.extras 112 119 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From120 : Window source012.plan source012.extras 120 127 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From128 : Window source012.plan source012.extras 128 135 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From136 : Window source012.plan source012.extras 136 143 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From144 : Window source012.plan source012.extras 144 151 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source012From152 : Window source012.plan source012.extras 152 152 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source012_valid : source012.Valid := by
  change source012.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source012From48 (join source012From56 source012From64)) (join (join source012From72 source012From80) (join source012From88 source012From96))) (join (join source012From104 (join source012From112 source012From120)) (join (join source012From128 source012From136) (join source012From144 source012From152))))

end JSP233.PopulationSources20258
