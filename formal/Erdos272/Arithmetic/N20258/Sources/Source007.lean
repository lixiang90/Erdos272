module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source007 : Source :=
  ⟨⟨48,115,19,4000,100,[
    (.marks 48 1 48 false,1501),
    (.marks 48 1 53 false,901),
    (.marks 48 1 56 false,1901),
    (.marks 48 1 62 false,2601),
    (.marks 48 1 68 false,3201),
    (.marks 48 1 71 false,301),
    (.marks 48 1 74 false,2201),
    (.marks 48 1 77 false,601),
    (.marks 48 1 80 false,3901),
    (.marks 48 1 86 false,3901),
    (.marks 48 1 89 false,9801),
    (.marks 48 1 92 false,17201),
    (.marks 48 1 95 false,14801),
    (.marks 48 1 98 false,19401),
    (.marks 48 1 101 false,17001),
    (.marks 48 1 104 false,19401),
    (.marks 48 1 107 false,19201),
    (.marks 48 1 110 false,21601),
    (.marks 48 1 113 false,19401),
    (.marks 48 1 115 false,13001),
    (.marks 48 2 48 false,368),
    (.marks 48 2 50 false,335),
    (.marks 48 2 53 false,35),
    (.marks 48 2 56 false,601),
    (.marks 48 2 59 false,1035),
    (.marks 48 2 62 false,601),
    (.marks 48 2 68 false,1401),
    (.marks 48 2 71 false,235),
    (.marks 48 2 74 false,2135),
    (.marks 48 2 77 false,11201),
    (.marks 48 2 80 false,12001),
    (.marks 48 2 83 false,14501),
    (.marks 48 2 86 false,11901),
    (.marks 48 2 89 false,5201),
    (.marks 48 3 48 false,285),
    (.marks 48 3 50 false,298),
    (.marks 48 3 53 false,388),
    (.marks 48 3 56 false,111),
    (.marks 48 3 59 false,508),
    (.marks 48 3 62 false,18),
    (.marks 48 3 65 false,485),
    (.marks 48 3 68 false,6651),
    (.marks 48 3 71 false,11068),
    (.marks 48 3 74 false,10068),
    (.marks 48 4 48 false,131),
    (.marks 48 4 50 false,251),
    (.marks 48 4 56 false,691),
    (.marks 48 4 62 false,3891),
    (.marks 48 4 65 false,9651),
    (.marks 48 4 68 false,2551),
    (.marks 48 5 50 false,161),
    (.marks 48 5 53 false,396),
    (.marks 48 5 56 false,68),
    (.marks 48 5 59 false,5161),
    (.marks 48 5 62 false,4761),
    (.marks 48 6 48 false,121),
    (.marks 48 6 50 false,162),
    (.marks 48 6 56 false,3278),
    (.marks 48 6 59 false,3401),
    (.marks 48 7 48 false,26),
    (.marks 48 7 50 false,51),
    (.marks 48 7 53 false,1687),
    (.marks 48 7 56 false,2859),
    (.marks 48 8 48 false,132),
    (.marks 48 8 50 false,107),
    (.marks 48 8 53 false,2846),
    (.marks 48 9 53 false,2066),
    (.marks 48 10 50 false,454),
    (.marks 48 10 53 false,893),
    (.marks 48 11 50 false,805),
    (.marks 48 12 48 false,238),
    (.marks 48 12 50 false,1521),
    (.marks 48 13 48 false,809),
    (.marks 48 13 50 false,1271)]⟩,
   []⟩

private theorem source007From48 : Window source007.plan source007.extras 48 55 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source007From56 : Window source007.plan source007.extras 56 63 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source007From64 : Window source007.plan source007.extras 64 71 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source007From72 : Window source007.plan source007.extras 72 79 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source007From80 : Window source007.plan source007.extras 80 87 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source007From88 : Window source007.plan source007.extras 88 95 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source007From96 : Window source007.plan source007.extras 96 103 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source007From104 : Window source007.plan source007.extras 104 111 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source007From112 : Window source007.plan source007.extras 112 115 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source007_valid : source007.Valid := by
  change source007.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source007From48 source007From56) (join source007From64 source007From72)) (join (join source007From80 source007From88) (join source007From96 (join source007From104 source007From112))))

end JSP233.PopulationSources20258
