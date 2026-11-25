module

public import Erdos272.Arithmetic.N19227.Prices
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def p101 : Source := ⟨⟨50,141,24,6000,100,[
  (.marks 50 1 50 false,668),
  (.marks 50 1 52 false,1135),
  (.marks 50 1 58 false,4201),
  (.marks 50 1 61 false,101),
  (.marks 50 1 64 false,1801),
  (.marks 50 1 67 false,701),
  (.marks 50 1 70 false,3101),
  (.marks 50 1 73 false,601),
  (.marks 50 1 76 false,2201),
  (.marks 50 1 82 false,4401),
  (.marks 50 1 88 false,3301),
  (.marks 50 1 94 false,4201),
  (.marks 50 1 97 false,1401),
  (.marks 50 1 100 false,4101),
  (.marks 50 1 106 false,6401),
  (.marks 50 1 109 false,13101),
  (.marks 50 1 112 false,22801),
  (.marks 50 1 115 false,17801),
  (.marks 50 1 118 false,22201),
  (.marks 50 1 121 false,20001),
  (.marks 50 1 124 false,23601),
  (.marks 50 1 127 false,22401),
  (.marks 50 1 130 false,25801),
  (.marks 50 1 133 false,21201),
  (.marks 50 1 136 false,26801),
  (.marks 50 1 139 false,22801),
  (.marks 50 1 141 false,14001),
  (.marks 50 2 50 false,735),
  (.marks 50 2 55 false,647),
  (.marks 50 2 58 false,956),
  (.marks 50 2 61 false,101),
  (.marks 50 2 64 false,601),
  (.marks 50 2 67 false,568),
  (.marks 50 2 70 false,1101),
  (.marks 50 2 73 false,301),
  (.marks 50 2 76 false,401),
  (.marks 50 2 79 false,1235),
  (.marks 50 2 82 false,668),
  (.marks 50 2 88 false,1468),
  (.marks 50 2 91 false,5301),
  (.marks 50 2 94 false,13201),
  (.marks 50 2 97 false,15401),
  (.marks 50 2 100 false,14401),
  (.marks 50 2 103 false,19101),
  (.marks 50 2 106 false,13801),
  (.marks 50 2 109 false,5101),
  (.marks 50 3 55 false,568),
  (.marks 50 3 61 false,701),
  (.marks 50 3 67 false,435),
  (.marks 50 3 70 false,301),
  (.marks 50 3 73 false,1001),
  (.marks 50 3 79 false,518),
  (.marks 50 3 82 false,6351),
  (.marks 50 3 85 false,14335),
  (.marks 50 3 88 false,11335),
  (.marks 50 3 91 false,10401),
  (.marks 50 4 50 false,81),
  (.marks 50 4 52 false,188),
  (.marks 50 4 55 false,595),
  (.marks 50 4 61 false,221),
  (.marks 50 4 64 false,441),
  (.marks 50 4 67 false,181),
  (.marks 50 4 70 false,81),
  (.marks 50 4 73 false,241),
  (.marks 50 4 76 false,9061),
  (.marks 50 4 79 false,11551),
  (.marks 50 4 82 false,4251),
  (.marks 50 5 52 false,106),
  (.marks 50 5 55 false,170),
  (.marks 50 5 61 false,710),
  (.marks 50 5 64 false,33),
  (.marks 50 5 67 false,155),
  (.marks 50 5 70 false,3588),
  (.marks 50 5 73 false,10861),
  (.marks 50 5 76 false,1441),
  (.marks 50 6 50 false,350),
  (.marks 50 6 52 false,248),
  (.marks 50 6 67 false,5954),
  (.marks 50 6 70 false,5235),
  (.marks 50 7 61 false,394),
  (.marks 50 7 64 false,3930),
  (.marks 50 7 67 false,3616),
  (.marks 50 8 50 false,79),
  (.marks 50 8 55 false,94),
  (.marks 50 8 61 false,1292),
  (.marks 50 8 64 false,4401),
  (.marks 50 9 50 false,1095),
  (.marks 50 9 55 false,503),
  (.marks 50 9 61 false,3895),
  (.marks 50 10 52 false,30),
  (.marks 50 10 55 false,433),
  (.marks 50 10 61 false,2996),
  (.marks 50 11 52 false,2101),
  (.marks 50 11 55 false,201),
  (.marks 50 11 58 false,2247),
  (.marks 50 12 55 false,201),
  (.marks 50 12 58 false,1648),
  (.marks 50 13 52 false,2001),
  (.marks 50 13 55 false,101),
  (.marks 50 13 58 false,1198),
  (.marks 50 14 55 false,1648),
  (.marks 50 14 58 false,759),
  (.marks 50 15 55 false,3305),
  (.marks 50 15 58 false,801),
  (.marks 50 16 55 false,1151),
  (.overlap 50 28 10 40,4401),
  (.overlap 50 29 10 40,9801),
  (.overlap 51 29 13 39,7001),
  (.overlap 51 30 13 39,19601),
  (.overlap 51 31 13 39,7801),
  (.overlap 52 31 16 38,15001),
  (.overlap 52 32 16 38,7801),
  (.overlap 53 32 19 37,5601),
  (.overlap 53 33 19 37,33001)]⟩,[]⟩

private theorem part50 : Window p101.plan p101.extras 50 57 :=
  window (g:=prices) (by decide +kernel)
private theorem part58 : Window p101.plan p101.extras 58 65 :=
  window (g:=prices) (by decide +kernel)
private theorem part66 : Window p101.plan p101.extras 66 73 :=
  window (g:=prices) (by decide +kernel)
private theorem part74 : Window p101.plan p101.extras 74 81 :=
  window (g:=prices) (by decide +kernel)
private theorem part82 : Window p101.plan p101.extras 82 89 :=
  window (g:=prices) (by decide +kernel)
private theorem part90 : Window p101.plan p101.extras 90 97 :=
  window (g:=prices) (by decide +kernel)
private theorem part98 : Window p101.plan p101.extras 98 105 :=
  window (g:=prices) (by decide +kernel)
private theorem part106 : Window p101.plan p101.extras 106 113 :=
  window (g:=prices) (by decide +kernel)
private theorem part114 : Window p101.plan p101.extras 114 121 :=
  window (g:=prices) (by decide +kernel)
private theorem part122 : Window p101.plan p101.extras 122 129 :=
  window (g:=prices) (by decide +kernel)
private theorem part130 : Window p101.plan p101.extras 130 137 :=
  window (g:=prices) (by decide +kernel)
private theorem part138 : Window p101.plan p101.extras 138 141 :=
  window (g:=prices) (by decide +kernel)

theorem p101_valid : p101.Valid := by
  change p101.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join part50 (join part58 part66)) (join part74 (join part82 part90))) (join (join part98 (join part106 part114)) (join part122 (join part130 part138))))

end JSP233.Credit19227
