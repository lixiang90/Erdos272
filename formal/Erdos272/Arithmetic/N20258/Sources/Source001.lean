module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source001 : Source :=
  ⟨⟨46,115,20,4000,100,[
    (.marks 46 1 46 false,2001),
    (.marks 46 1 54 false,2835),
    (.marks 46 1 57 false,68),
    (.marks 46 1 60 false,2501),
    (.marks 46 1 66 false,2001),
    (.marks 46 1 72 false,3701),
    (.marks 46 1 78 false,4501),
    (.marks 46 1 84 false,3201),
    (.marks 46 1 90 false,17701),
    (.marks 46 1 93 false,14801),
    (.marks 46 1 96 false,19601),
    (.marks 46 1 99 false,14001),
    (.marks 46 1 102 false,23001),
    (.marks 46 1 105 false,14601),
    (.marks 46 1 108 false,24601),
    (.marks 46 1 111 false,15801),
    (.marks 46 1 114 false,23201),
    (.marks 46 1 115 false,4401),
    (.marks 46 2 46 false,635),
    (.marks 46 2 48 false,501),
    (.marks 46 2 54 false,835),
    (.marks 46 2 60 false,1701),
    (.marks 46 2 63 false,68),
    (.marks 46 2 66 false,668),
    (.marks 46 2 72 false,1935),
    (.marks 46 2 75 false,5168),
    (.marks 46 2 78 false,10801),
    (.marks 46 2 81 false,12901),
    (.marks 46 2 84 false,13401),
    (.marks 46 2 87 false,13601),
    (.marks 46 2 90 false,301),
    (.marks 46 3 48 false,118),
    (.marks 46 3 51 false,251),
    (.marks 46 3 54 false,525),
    (.marks 46 3 57 false,295),
    (.marks 46 3 60 false,301),
    (.marks 46 3 63 false,335),
    (.marks 46 3 69 false,11485),
    (.marks 46 3 72 false,8468),
    (.marks 46 3 75 false,7935),
    (.marks 46 4 46 false,28),
    (.marks 46 4 48 false,285),
    (.marks 46 4 51 false,311),
    (.marks 46 4 54 false,291),
    (.marks 46 4 60 false,541),
    (.marks 46 4 63 false,7241),
    (.marks 46 4 66 false,8201),
    (.marks 46 4 69 false,451),
    (.marks 46 5 48 false,41),
    (.marks 46 5 51 false,308),
    (.marks 46 5 54 false,55),
    (.marks 46 5 57 false,441),
    (.marks 46 5 60 false,6595),
    (.marks 46 5 63 false,3161),
    (.marks 46 6 46 false,127),
    (.marks 46 6 48 false,219),
    (.marks 46 6 51 false,249),
    (.marks 46 6 54 false,182),
    (.marks 46 6 57 false,6230),
    (.marks 46 6 60 false,168),
    (.marks 46 7 48 false,186),
    (.marks 46 7 51 false,109),
    (.marks 46 7 54 false,2862),
    (.marks 46 7 57 false,1573),
    (.marks 46 8 46 false,205),
    (.marks 46 8 48 false,182),
    (.marks 46 8 54 false,3004),
    (.marks 46 9 51 false,2028),
    (.marks 46 9 54 false,24),
    (.marks 46 10 51 false,1423),
    (.marks 46 11 51 false,986),
    (.marks 46 12 46 false,97),
    (.marks 46 12 48 false,1618),
    (.marks 46 12 51 false,1277),
    (.marks 46 13 48 false,721),
    (.marks 46 13 51 false,1271),
    (.marks 46 14 46 false,97),
    (.marks 46 14 48 false,1017),
    (.marks 46 15 46 false,359),
    (.marks 46 15 48 false,428),
    (.marks 46 16 46 false,364)]⟩,
   []⟩

private theorem source001From46 : Window source001.plan source001.extras 46 53 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source001From54 : Window source001.plan source001.extras 54 61 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source001From62 : Window source001.plan source001.extras 62 69 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source001From70 : Window source001.plan source001.extras 70 77 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source001From78 : Window source001.plan source001.extras 78 85 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source001From86 : Window source001.plan source001.extras 86 93 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source001From94 : Window source001.plan source001.extras 94 101 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source001From102 : Window source001.plan source001.extras 102 109 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source001From110 : Window source001.plan source001.extras 110 115 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source001_valid : source001.Valid := by
  change source001.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source001From46 source001From54) (join source001From62 source001From70)) (join (join source001From78 source001From86) (join source001From94 (join source001From102 source001From110))))

end JSP233.PopulationSources20258
