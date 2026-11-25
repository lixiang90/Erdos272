module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source120 : Source :=
  ⟨⟨68,208,30,13000,100,[
    (.marks 68 1 68 false,561),
    (.marks 68 1 70 false,2541),
    (.marks 68 1 73 false,601),
    (.marks 68 1 76 false,2201),
    (.marks 68 1 82 false,4401),
    (.marks 68 1 88 false,3301),
    (.marks 68 1 94 false,4201),
    (.marks 68 1 97 false,1401),
    (.marks 68 1 100 false,4501),
    (.marks 68 1 106 false,4001),
    (.marks 68 1 112 false,4501),
    (.marks 68 1 118 false,5901),
    (.marks 68 1 121 false,1601),
    (.marks 68 1 124 false,4401),
    (.marks 68 1 127 false,1101),
    (.marks 68 1 130 false,5401),
    (.marks 68 1 136 false,4101),
    (.marks 68 1 142 false,8101),
    (.marks 68 1 145 false,701),
    (.marks 68 1 148 false,6901),
    (.marks 68 1 154 false,4101),
    (.marks 68 1 157 false,5701),
    (.marks 68 1 160 false,29601),
    (.marks 68 1 163 false,29401),
    (.marks 68 1 166 false,32401),
    (.marks 68 1 169 false,26601),
    (.marks 68 1 172 false,36001),
    (.marks 68 1 175 false,25401),
    (.marks 68 1 178 false,37801),
    (.marks 68 1 181 false,29801),
    (.marks 68 1 184 false,34801),
    (.marks 68 1 187 false,31001),
    (.marks 68 1 190 false,36601),
    (.marks 68 1 193 false,35001),
    (.marks 68 1 196 false,37201),
    (.marks 68 1 199 false,33601),
    (.marks 68 1 202 false,39601),
    (.marks 68 1 205 false,32401),
    (.marks 68 1 208 false,24801),
    (.marks 68 2 68 false,1101),
    (.marks 68 2 73 false,488),
    (.marks 68 2 76 false,361),
    (.marks 68 2 79 false,1921),
    (.marks 68 2 82 false,601),
    (.marks 68 2 85 false,801),
    (.marks 68 2 91 false,2201),
    (.marks 68 2 100 false,868),
    (.marks 68 2 103 false,1635),
    (.marks 68 2 109 false,2001),
    (.marks 68 2 112 false,268),
    (.marks 68 2 115 false,835),
    (.marks 68 2 127 false,1701),
    (.marks 68 2 130 false,101),
    (.marks 68 2 133 false,11268),
    (.marks 68 2 136 false,18601),
    (.marks 68 2 139 false,26901),
    (.marks 68 2 142 false,19701),
    (.marks 68 2 145 false,22301),
    (.marks 68 2 148 false,21001),
    (.marks 68 2 151 false,28101),
    (.marks 68 2 154 false,23101),
    (.marks 68 2 157 false,22301),
    (.marks 68 3 68 false,381),
    (.marks 68 3 73 false,1055),
    (.marks 68 3 115 false,601),
    (.marks 68 3 118 false,13101),
    (.marks 68 3 121 false,18401),
    (.marks 68 3 124 false,19201),
    (.marks 68 3 127 false,19601),
    (.marks 68 3 130 false,20001),
    (.marks 68 3 133 false,10235),
    (.marks 68 4 97 false,81),
    (.marks 68 4 103 false,401),
    (.marks 68 4 106 false,3901),
    (.marks 68 4 109 false,18201),
    (.marks 68 4 112 false,15735),
    (.marks 68 4 115 false,18668),
    (.marks 68 4 118 false,3201),
    (.marks 68 5 91 false,168),
    (.marks 68 5 97 false,521),
    (.marks 68 5 100 false,11568),
    (.marks 68 5 103 false,16668),
    (.marks 68 5 106 false,10301),
    (.marks 68 6 85 false,501),
    (.marks 68 6 88 false,201),
    (.marks 68 6 91 false,235),
    (.marks 68 6 94 false,9787),
    (.marks 68 6 97 false,14801),
    (.marks 68 6 100 false,1968),
    (.marks 68 7 73 false,181),
    (.marks 68 7 76 false,141),
    (.marks 68 7 79 false,381),
    (.marks 68 7 85 false,301),
    (.marks 68 7 88 false,2601),
    (.marks 68 7 91 false,13101),
    (.marks 68 7 94 false,3416),
    (.marks 68 8 73 false,301),
    (.marks 68 8 76 false,101),
    (.marks 68 8 79 false,201),
    (.marks 68 8 85 false,4357),
    (.marks 68 8 88 false,10001),
    (.marks 68 9 73 false,401),
    (.marks 68 9 76 false,101),
    (.marks 68 9 79 false,101),
    (.marks 68 9 82 false,3101),
    (.marks 68 9 85 false,7746),
    (.marks 68 10 73 false,201),
    (.marks 68 10 76 false,201),
    (.marks 68 10 79 false,301),
    (.marks 68 10 82 false,8120),
    (.marks 68 11 73 false,401),
    (.marks 68 11 76 false,101),
    (.marks 68 11 79 false,6368),
    (.marks 68 11 82 false,83),
    (.marks 68 12 70 false,121),
    (.marks 68 12 73 false,181),
    (.marks 68 12 76 false,1201),
    (.marks 68 12 79 false,4035),
    (.marks 68 13 70 false,201),
    (.marks 68 13 73 false,101),
    (.marks 68 13 76 false,4044),
    (.marks 68 14 70 false,101),
    (.marks 68 14 73 false,201),
    (.marks 68 14 76 false,3092),
    (.marks 68 15 70 false,201),
    (.marks 68 15 73 false,1051),
    (.marks 68 15 76 false,1568),
    (.marks 68 16 70 false,101),
    (.marks 68 16 73 false,1981),
    (.marks 68 17 70 false,301),
    (.marks 68 17 73 false,1450),
    (.marks 68 18 73 false,1203),
    (.marks 68 19 68 false,921),
    (.marks 68 19 70 false,1411),
    (.marks 68 19 73 false,723),
    (.marks 68 20 68 false,175),
    (.marks 68 20 70 false,422),
    (.marks 68 20 73 false,1825),
    (.marks 68 21 70 false,614),
    (.marks 68 21 73 false,678),
    (.marks 68 22 70 false,483),
    (.marks 68 23 68 false,243),
    (.marks 68 23 70 false,2717),
    (.marks 68 24 68 false,826)]⟩,
   []⟩

private theorem source120From68 : Window source120.plan source120.extras 68 75 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From76 : Window source120.plan source120.extras 76 83 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From84 : Window source120.plan source120.extras 84 91 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From92 : Window source120.plan source120.extras 92 99 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From100 : Window source120.plan source120.extras 100 107 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From108 : Window source120.plan source120.extras 108 115 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From116 : Window source120.plan source120.extras 116 123 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From124 : Window source120.plan source120.extras 124 131 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From132 : Window source120.plan source120.extras 132 139 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From140 : Window source120.plan source120.extras 140 147 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From148 : Window source120.plan source120.extras 148 155 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From156 : Window source120.plan source120.extras 156 163 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From164 : Window source120.plan source120.extras 164 171 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From172 : Window source120.plan source120.extras 172 179 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From180 : Window source120.plan source120.extras 180 187 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From188 : Window source120.plan source120.extras 188 195 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From196 : Window source120.plan source120.extras 196 203 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source120From204 : Window source120.plan source120.extras 204 208 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source120_valid : source120.Valid := by
  change source120.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join (join source120From68 source120From76) (join source120From84 source120From92)) (join (join source120From100 source120From108) (join source120From116 (join source120From124 source120From132)))) (join (join (join source120From140 source120From148) (join source120From156 source120From164)) (join (join source120From172 source120From180) (join source120From188 (join source120From196 source120From204)))))

end JSP233.PopulationSources20258
