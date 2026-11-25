module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source003 : Source :=
  ⟨⟨47,115,20,4000,100,[
    (.marks 47 1 52 false,1001),
    (.marks 47 1 58 false,4201),
    (.marks 47 1 61 false,101),
    (.marks 47 1 64 false,1801),
    (.marks 47 1 67 false,701),
    (.marks 47 1 70 false,3101),
    (.marks 47 1 73 false,601),
    (.marks 47 1 76 false,2201),
    (.marks 47 1 82 false,4401),
    (.marks 47 1 88 false,8501),
    (.marks 47 1 91 false,13801),
    (.marks 47 1 94 false,17401),
    (.marks 47 1 97 false,16801),
    (.marks 47 1 100 false,19601),
    (.marks 47 1 103 false,18001),
    (.marks 47 1 106 false,20201),
    (.marks 47 1 109 false,18201),
    (.marks 47 1 112 false,22801),
    (.marks 47 1 115 false,16601),
    (.marks 47 2 52 false,868),
    (.marks 47 2 55 false,535),
    (.marks 47 2 58 false,1068),
    (.marks 47 2 61 false,101),
    (.marks 47 2 64 false,601),
    (.marks 47 2 67 false,568),
    (.marks 47 2 70 false,1101),
    (.marks 47 2 73 false,135),
    (.marks 47 2 76 false,8501),
    (.marks 47 2 79 false,13301),
    (.marks 47 2 82 false,11901),
    (.marks 47 2 85 false,13701),
    (.marks 47 2 88 false,9501),
    (.marks 47 3 49 false,201),
    (.marks 47 3 52 false,635),
    (.marks 47 3 55 false,568),
    (.marks 47 3 58 false,35),
    (.marks 47 3 61 false,701),
    (.marks 47 3 67 false,4135),
    (.marks 47 3 70 false,9201),
    (.marks 47 3 73 false,12268),
    (.marks 47 3 76 false,2401),
    (.marks 47 4 52 false,301),
    (.marks 47 4 55 false,421),
    (.marks 47 4 58 false,141),
    (.marks 47 4 61 false,1021),
    (.marks 47 4 64 false,8801),
    (.marks 47 4 67 false,6201),
    (.marks 47 5 49 false,468),
    (.marks 47 5 52 false,101),
    (.marks 47 5 55 false,315),
    (.marks 47 5 58 false,1495),
    (.marks 47 5 61 false,8481),
    (.marks 47 6 52 false,321),
    (.marks 47 6 55 false,1597),
    (.marks 47 6 58 false,4868),
    (.marks 47 7 49 false,185),
    (.marks 47 7 52 false,282),
    (.marks 47 7 55 false,4323),
    (.marks 47 8 49 false,40),
    (.marks 47 8 52 false,1235),
    (.marks 47 8 55 false,1851),
    (.marks 47 9 49 false,313),
    (.marks 47 9 52 false,1868),
    (.marks 47 10 49 false,501),
    (.marks 47 10 52 false,1238),
    (.marks 47 11 49 false,501),
    (.marks 47 11 52 false,832),
    (.marks 47 12 47 false,248),
    (.marks 47 12 49 false,1725),
    (.marks 47 12 52 false,135),
    (.marks 47 13 49 false,2004),
    (.marks 47 14 47 false,929),
    (.marks 47 14 49 false,76),
    (.marks 47 15 47 false,428)]⟩,
   []⟩

private theorem source003From47 : Window source003.plan source003.extras 47 54 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source003From55 : Window source003.plan source003.extras 55 62 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source003From63 : Window source003.plan source003.extras 63 70 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source003From71 : Window source003.plan source003.extras 71 78 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source003From79 : Window source003.plan source003.extras 79 86 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source003From87 : Window source003.plan source003.extras 87 94 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source003From95 : Window source003.plan source003.extras 95 102 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source003From103 : Window source003.plan source003.extras 103 110 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source003From111 : Window source003.plan source003.extras 111 115 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source003_valid : source003.Valid := by
  change source003.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source003From47 source003From55) (join source003From63 source003From71)) (join (join source003From79 source003From87) (join source003From95 (join source003From103 source003From111))))

end JSP233.PopulationSources20258
