module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source004 : Source :=
  ⟨⟨47,141,26,6000,100,[
    (.marks 47 1 52 false,1001),
    (.marks 47 1 58 false,4201),
    (.marks 47 1 61 false,101),
    (.marks 47 1 64 false,1801),
    (.marks 47 1 67 false,701),
    (.marks 47 1 70 false,3101),
    (.marks 47 1 73 false,601),
    (.marks 47 1 76 false,2201),
    (.marks 47 1 82 false,4401),
    (.marks 47 1 88 false,3301),
    (.marks 47 1 94 false,4201),
    (.marks 47 1 97 false,1401),
    (.marks 47 1 100 false,4101),
    (.marks 47 1 106 false,6401),
    (.marks 47 1 109 false,13101),
    (.marks 47 1 112 false,22801),
    (.marks 47 1 115 false,17801),
    (.marks 47 1 118 false,22201),
    (.marks 47 1 121 false,20001),
    (.marks 47 1 124 false,23601),
    (.marks 47 1 127 false,22401),
    (.marks 47 1 130 false,25801),
    (.marks 47 1 133 false,21201),
    (.marks 47 1 136 false,26801),
    (.marks 47 1 139 false,22801),
    (.marks 47 1 141 false,14001),
    (.marks 47 2 52 false,868),
    (.marks 47 2 55 false,647),
    (.marks 47 2 58 false,956),
    (.marks 47 2 61 false,101),
    (.marks 47 2 64 false,601),
    (.marks 47 2 67 false,568),
    (.marks 47 2 70 false,1101),
    (.marks 47 2 73 false,301),
    (.marks 47 2 76 false,401),
    (.marks 47 2 79 false,1235),
    (.marks 47 2 82 false,668),
    (.marks 47 2 88 false,1468),
    (.marks 47 2 91 false,5301),
    (.marks 47 2 94 false,13201),
    (.marks 47 2 97 false,15401),
    (.marks 47 2 100 false,14401),
    (.marks 47 2 103 false,19101),
    (.marks 47 2 106 false,13801),
    (.marks 47 2 109 false,5101),
    (.marks 47 3 49 false,201),
    (.marks 47 3 52 false,635),
    (.marks 47 3 55 false,601),
    (.marks 47 3 61 false,701),
    (.marks 47 3 67 false,435),
    (.marks 47 3 70 false,301),
    (.marks 47 3 73 false,1001),
    (.marks 47 3 79 false,518),
    (.marks 47 3 82 false,6351),
    (.marks 47 3 85 false,14335),
    (.marks 47 3 88 false,11335),
    (.marks 47 3 91 false,10401),
    (.marks 47 4 47 false,1601),
    (.marks 47 4 49 false,1481),
    (.marks 47 4 52 false,301),
    (.marks 47 4 55 false,561),
    (.marks 47 4 61 false,221),
    (.marks 47 4 64 false,441),
    (.marks 47 4 67 false,181),
    (.marks 47 4 70 false,81),
    (.marks 47 4 73 false,241),
    (.marks 47 4 76 false,9061),
    (.marks 47 4 79 false,11551),
    (.marks 47 4 82 false,4251),
    (.marks 47 5 49 false,155),
    (.marks 47 5 52 false,106),
    (.marks 47 5 55 false,170),
    (.marks 47 5 61 false,710),
    (.marks 47 5 64 false,33),
    (.marks 47 5 67 false,155),
    (.marks 47 5 70 false,3588),
    (.marks 47 5 73 false,10861),
    (.marks 47 5 76 false,1441),
    (.marks 47 6 49 false,1140),
    (.marks 47 6 52 false,597),
    (.marks 47 6 67 false,5954),
    (.marks 47 6 70 false,5235),
    (.marks 47 7 49 false,3030),
    (.marks 47 7 61 false,394),
    (.marks 47 7 64 false,3930),
    (.marks 47 7 67 false,3616),
    (.marks 47 8 52 false,79),
    (.marks 47 8 55 false,94),
    (.marks 47 8 61 false,1292),
    (.marks 47 8 64 false,4401),
    (.marks 47 9 52 false,1024),
    (.marks 47 9 55 false,575),
    (.marks 47 9 61 false,3895),
    (.marks 47 10 52 false,2229),
    (.marks 47 10 55 false,361),
    (.marks 47 10 61 false,2996),
    (.marks 47 11 55 false,174),
    (.marks 47 11 58 false,2247),
    (.marks 47 12 52 false,1974),
    (.marks 47 12 55 false,229),
    (.marks 47 12 58 false,1648),
    (.marks 47 13 55 false,101),
    (.marks 47 13 58 false,1198),
    (.marks 47 14 55 false,1648),
    (.marks 47 14 58 false,759),
    (.marks 47 15 55 false,3305),
    (.marks 47 15 58 false,801),
    (.marks 47 16 55 false,1151),
    (.overlap 47 22 5 42,6601),
    (.overlap 47 23 5 42,25001),
    (.overlap 48 24 8 41,29801),
    (.overlap 49 24 10 41,23001),
    (.overlap 49 25 10 41,601),
    (.overlap 49 26 10 41,15001),
    (.overlap 50 26 13 40,7001),
    (.overlap 50 27 13 40,7201),
    (.overlap 51 27 15 40,7201),
    (.overlap 51 28 15 40,16601),
    (.overlap 51 29 15 40,7401),
    (.overlap 52 29 18 39,7201),
    (.overlap 52 30 18 39,18801),
    (.overlap 53 31 22 37,1201),
    (.overlap 53 32 22 37,18201),
    (.overlap 53 33 22 37,19201)]⟩,
   []⟩

private theorem source004From47 : Window source004.plan source004.extras 47 54 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source004From55 : Window source004.plan source004.extras 55 62 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source004From63 : Window source004.plan source004.extras 63 70 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source004From71 : Window source004.plan source004.extras 71 78 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source004From79 : Window source004.plan source004.extras 79 86 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source004From87 : Window source004.plan source004.extras 87 94 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source004From95 : Window source004.plan source004.extras 95 102 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source004From103 : Window source004.plan source004.extras 103 110 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source004From111 : Window source004.plan source004.extras 111 118 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source004From119 : Window source004.plan source004.extras 119 126 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source004From127 : Window source004.plan source004.extras 127 134 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source004From135 : Window source004.plan source004.extras 135 141 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source004_valid : source004.Valid := by
  change source004.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source004From47 (join source004From55 source004From63)) (join source004From71 (join source004From79 source004From87))) (join (join source004From95 (join source004From103 source004From111)) (join source004From119 (join source004From127 source004From135))))

end JSP233.PopulationSources20258
