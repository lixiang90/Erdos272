module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source111 : Source :=
  ⟨⟨62,208,33,13000,100,[
    (.marks 62 1 62 false,268),
    (.marks 62 1 64 false,1535),
    (.marks 62 1 67 false,701),
    (.marks 62 1 70 false,3101),
    (.marks 62 1 73 false,601),
    (.marks 62 1 76 false,2201),
    (.marks 62 1 82 false,4401),
    (.marks 62 1 88 false,3301),
    (.marks 62 1 94 false,4201),
    (.marks 62 1 97 false,1401),
    (.marks 62 1 100 false,4501),
    (.marks 62 1 106 false,4001),
    (.marks 62 1 112 false,4501),
    (.marks 62 1 118 false,5901),
    (.marks 62 1 121 false,1601),
    (.marks 62 1 124 false,4401),
    (.marks 62 1 127 false,1101),
    (.marks 62 1 130 false,5401),
    (.marks 62 1 136 false,4101),
    (.marks 62 1 142 false,8101),
    (.marks 62 1 145 false,701),
    (.marks 62 1 148 false,6901),
    (.marks 62 1 154 false,4101),
    (.marks 62 1 157 false,5701),
    (.marks 62 1 160 false,29601),
    (.marks 62 1 163 false,29401),
    (.marks 62 1 166 false,32401),
    (.marks 62 1 169 false,26601),
    (.marks 62 1 172 false,36001),
    (.marks 62 1 175 false,25401),
    (.marks 62 1 178 false,37801),
    (.marks 62 1 181 false,29801),
    (.marks 62 1 184 false,34801),
    (.marks 62 1 187 false,31001),
    (.marks 62 1 190 false,36601),
    (.marks 62 1 193 false,35001),
    (.marks 62 1 196 false,37201),
    (.marks 62 1 199 false,33601),
    (.marks 62 1 202 false,39601),
    (.marks 62 1 205 false,32401),
    (.marks 62 1 208 false,24801),
    (.marks 62 2 62 false,801),
    (.marks 62 2 67 false,868),
    (.marks 62 2 70 false,801),
    (.marks 62 2 73 false,868),
    (.marks 62 2 76 false,201),
    (.marks 62 2 79 false,1901),
    (.marks 62 2 82 false,401),
    (.marks 62 2 85 false,801),
    (.marks 62 2 91 false,2201),
    (.marks 62 2 100 false,868),
    (.marks 62 2 103 false,1635),
    (.marks 62 2 109 false,2001),
    (.marks 62 2 112 false,268),
    (.marks 62 2 115 false,835),
    (.marks 62 2 127 false,1701),
    (.marks 62 2 130 false,101),
    (.marks 62 2 133 false,11268),
    (.marks 62 2 136 false,18601),
    (.marks 62 2 139 false,26901),
    (.marks 62 2 142 false,19701),
    (.marks 62 2 145 false,22301),
    (.marks 62 2 148 false,21001),
    (.marks 62 2 151 false,28101),
    (.marks 62 2 154 false,23101),
    (.marks 62 2 157 false,22301),
    (.marks 62 3 64 false,368),
    (.marks 62 3 67 false,468),
    (.marks 62 3 73 false,835),
    (.marks 62 3 115 false,601),
    (.marks 62 3 118 false,13101),
    (.marks 62 3 121 false,18401),
    (.marks 62 3 124 false,19201),
    (.marks 62 3 127 false,19601),
    (.marks 62 3 130 false,20001),
    (.marks 62 3 133 false,10235),
    (.marks 62 4 62 false,2335),
    (.marks 62 4 64 false,388),
    (.marks 62 4 97 false,301),
    (.marks 62 4 103 false,401),
    (.marks 62 4 106 false,3901),
    (.marks 62 4 109 false,18201),
    (.marks 62 4 112 false,15735),
    (.marks 62 4 115 false,18668),
    (.marks 62 4 118 false,3201),
    (.marks 62 5 64 false,3448),
    (.marks 62 5 73 false,368),
    (.marks 62 5 85 false,301),
    (.marks 62 5 88 false,101),
    (.marks 62 5 91 false,301),
    (.marks 62 5 97 false,301),
    (.marks 62 5 100 false,11568),
    (.marks 62 5 103 false,16668),
    (.marks 62 5 106 false,10301),
    (.marks 62 6 64 false,2068),
    (.marks 62 6 67 false,368),
    (.marks 62 6 73 false,35),
    (.marks 62 6 79 false,301),
    (.marks 62 6 85 false,401),
    (.marks 62 6 88 false,101),
    (.marks 62 6 91 false,101),
    (.marks 62 6 94 false,9787),
    (.marks 62 6 97 false,14801),
    (.marks 62 6 100 false,1968),
    (.marks 62 7 67 false,3101),
    (.marks 62 7 73 false,301),
    (.marks 62 7 76 false,301),
    (.marks 62 7 79 false,101),
    (.marks 62 7 85 false,301),
    (.marks 62 7 88 false,2601),
    (.marks 62 7 91 false,13101),
    (.marks 62 7 94 false,3416),
    (.marks 62 8 67 false,101),
    (.marks 62 8 70 false,201),
    (.marks 62 8 73 false,101),
    (.marks 62 8 76 false,101),
    (.marks 62 8 79 false,201),
    (.marks 62 8 82 false,201),
    (.marks 62 8 85 false,4157),
    (.marks 62 8 88 false,10001),
    (.marks 62 9 67 false,3001),
    (.marks 62 9 70 false,101),
    (.marks 62 9 73 false,301),
    (.marks 62 9 76 false,101),
    (.marks 62 9 79 false,101),
    (.marks 62 9 82 false,3101),
    (.marks 62 9 85 false,7746),
    (.marks 62 10 67 false,3001),
    (.marks 62 10 70 false,101),
    (.marks 62 10 73 false,101),
    (.marks 62 10 76 false,201),
    (.marks 62 10 79 false,301),
    (.marks 62 10 82 false,8120),
    (.marks 62 11 70 false,201),
    (.marks 62 11 73 false,201),
    (.marks 62 11 76 false,101),
    (.marks 62 11 79 false,6368),
    (.marks 62 11 82 false,83),
    (.marks 62 12 70 false,3001),
    (.marks 62 12 73 false,101),
    (.marks 62 12 76 false,1201),
    (.marks 62 12 79 false,4035),
    (.marks 62 13 70 false,3001),
    (.marks 62 13 73 false,101),
    (.marks 62 13 76 false,4044),
    (.marks 62 14 70 false,101),
    (.marks 62 14 73 false,201),
    (.marks 62 14 76 false,3092),
    (.marks 62 15 70 false,2801),
    (.marks 62 15 73 false,1051),
    (.marks 62 15 76 false,1568),
    (.marks 62 16 73 false,1981),
    (.marks 62 17 73 false,1450),
    (.marks 62 18 73 false,3803),
    (.marks 62 19 73 false,623),
    (.overlap 62 30 5 57,22601),
    (.overlap 62 31 5 57,8801),
    (.overlap 63 31 7 57,16801),
    (.overlap 63 32 7 57,49201),
    (.overlap 64 32 9 57,13201),
    (.overlap 64 33 9 57,24001),
    (.overlap 64 34 9 57,3401),
    (.overlap 65 34 11 57,24601),
    (.overlap 65 35 11 57,19401),
    (.overlap 66 35 14 56,3001),
    (.overlap 66 36 14 56,16201),
    (.overlap 67 36 16 56,17401),
    (.overlap 67 37 16 56,26001),
    (.overlap 67 38 16 56,1001),
    (.overlap 68 38 19 55,23401),
    (.overlap 68 39 19 55,26001),
    (.overlap 69 39 21 55,2601),
    (.overlap 69 40 21 55,28201),
    (.overlap 69 41 21 55,16701),
    (.overlap 70 41 24 54,32701),
    (.overlap 70 42 24 54,9601),
    (.overlap 70 43 24 54,8401),
    (.overlap 71 44 28 52,10601),
    (.overlap 71 45 28 52,20801),
    (.overlap 71 46 28 52,18601)]⟩,
   []⟩

private theorem source111From62 : Window source111.plan source111.extras 62 69 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From70 : Window source111.plan source111.extras 70 77 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From78 : Window source111.plan source111.extras 78 85 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From86 : Window source111.plan source111.extras 86 93 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From94 : Window source111.plan source111.extras 94 101 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From102 : Window source111.plan source111.extras 102 109 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From110 : Window source111.plan source111.extras 110 117 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From118 : Window source111.plan source111.extras 118 125 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From126 : Window source111.plan source111.extras 126 133 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From134 : Window source111.plan source111.extras 134 141 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From142 : Window source111.plan source111.extras 142 149 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From150 : Window source111.plan source111.extras 150 157 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From158 : Window source111.plan source111.extras 158 165 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From166 : Window source111.plan source111.extras 166 173 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From174 : Window source111.plan source111.extras 174 181 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From182 : Window source111.plan source111.extras 182 189 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From190 : Window source111.plan source111.extras 190 197 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From198 : Window source111.plan source111.extras 198 205 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source111From206 : Window source111.plan source111.extras 206 208 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source111_valid : source111.Valid := by
  change source111.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join (join source111From62 source111From70) (join source111From78 source111From86)) (join (join source111From94 source111From102) (join source111From110 (join source111From118 source111From126)))) (join (join (join source111From134 source111From142) (join source111From150 (join source111From158 source111From166))) (join (join source111From174 source111From182) (join source111From190 (join source111From198 source111From206)))))

end JSP233.PopulationSources20258
