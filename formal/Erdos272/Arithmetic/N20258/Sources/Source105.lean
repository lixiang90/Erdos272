module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source105 : Source :=
  ⟨⟨60,199,32,12000,100,[
    (.marks 60 1 60 false,2601),
    (.marks 60 1 68 false,3201),
    (.marks 60 1 71 false,301),
    (.marks 60 1 74 false,2201),
    (.marks 60 1 77 false,601),
    (.marks 60 1 80 false,4001),
    (.marks 60 1 83 false,301),
    (.marks 60 1 86 false,3501),
    (.marks 60 1 89 false,1001),
    (.marks 60 1 92 false,2701),
    (.marks 60 1 98 false,4301),
    (.marks 60 1 101 false,1201),
    (.marks 60 1 104 false,2401),
    (.marks 60 1 107 false,2401),
    (.marks 60 1 110 false,3568),
    (.marks 60 1 113 false,1135),
    (.marks 60 1 116 false,4601),
    (.marks 60 1 122 false,5001),
    (.marks 60 1 128 false,6301),
    (.marks 60 1 134 false,4501),
    (.marks 60 1 137 false,2701),
    (.marks 60 1 140 false,4701),
    (.marks 60 1 143 false,201),
    (.marks 60 1 146 false,6201),
    (.marks 60 1 149 false,1201),
    (.marks 60 1 152 false,18901),
    (.marks 60 1 155 false,22601),
    (.marks 60 1 158 false,33401),
    (.marks 60 1 161 false,24801),
    (.marks 60 1 164 false,31801),
    (.marks 60 1 167 false,29401),
    (.marks 60 1 170 false,32401),
    (.marks 60 1 173 false,31001),
    (.marks 60 1 176 false,31201),
    (.marks 60 1 179 false,31201),
    (.marks 60 1 182 false,36801),
    (.marks 60 1 185 false,29001),
    (.marks 60 1 188 false,35601),
    (.marks 60 1 191 false,32401),
    (.marks 60 1 194 false,38001),
    (.marks 60 1 197 false,33801),
    (.marks 60 1 199 false,24401),
    (.marks 60 2 60 false,335),
    (.marks 60 2 62 false,268),
    (.marks 60 2 68 false,1401),
    (.marks 60 2 71 false,635),
    (.marks 60 2 74 false,1801),
    (.marks 60 2 77 false,201),
    (.marks 60 2 80 false,901),
    (.marks 60 2 83 false,1401),
    (.marks 60 2 89 false,801),
    (.marks 60 2 95 false,1301),
    (.marks 60 2 98 false,1001),
    (.marks 60 2 104 false,1935),
    (.marks 60 2 107 false,335),
    (.marks 60 2 110 false,1235),
    (.marks 60 2 116 false,868),
    (.marks 60 2 119 false,201),
    (.marks 60 2 125 false,1001),
    (.marks 60 2 128 false,10401),
    (.marks 60 2 131 false,21901),
    (.marks 60 2 134 false,19701),
    (.marks 60 2 137 false,21501),
    (.marks 60 2 140 false,22701),
    (.marks 60 2 143 false,23401),
    (.marks 60 2 146 false,20201),
    (.marks 60 2 149 false,24601),
    (.marks 60 2 152 false,12501),
    (.marks 60 3 60 false,68),
    (.marks 60 3 62 false,278),
    (.marks 60 3 65 false,1049),
    (.marks 60 3 68 false,121),
    (.marks 60 3 71 false,308),
    (.marks 60 3 113 false,11201),
    (.marks 60 3 116 false,15635),
    (.marks 60 3 119 false,18301),
    (.marks 60 3 122 false,18801),
    (.marks 60 3 125 false,19201),
    (.marks 60 3 128 false,10001),
    (.marks 60 4 60 false,201),
    (.marks 60 4 62 false,491),
    (.marks 60 4 95 false,201),
    (.marks 60 4 101 false,401),
    (.marks 60 4 104 false,14468),
    (.marks 60 4 107 false,16468),
    (.marks 60 4 110 false,16801),
    (.marks 60 4 113 false,7068),
    (.marks 60 5 71 false,161),
    (.marks 60 5 83 false,401),
    (.marks 60 5 89 false,101),
    (.marks 60 5 92 false,301),
    (.marks 60 5 95 false,5401),
    (.marks 60 5 98 false,14101),
    (.marks 60 5 101 false,15401),
    (.marks 60 5 104 false,601),
    (.marks 60 6 62 false,6),
    (.marks 60 6 71 false,268),
    (.marks 60 6 74 false,101),
    (.marks 60 6 77 false,201),
    (.marks 60 6 83 false,301),
    (.marks 60 6 89 false,2473),
    (.marks 60 6 92 false,13401),
    (.marks 60 6 95 false,8701),
    (.marks 60 7 65 false,41),
    (.marks 60 7 71 false,216),
    (.marks 60 7 74 false,101),
    (.marks 60 7 77 false,101),
    (.marks 60 7 83 false,401),
    (.marks 60 7 86 false,6801),
    (.marks 60 7 89 false,10630),
    (.marks 60 8 65 false,76),
    (.marks 60 8 71 false,201),
    (.marks 60 8 74 false,201),
    (.marks 60 8 77 false,301),
    (.marks 60 8 80 false,101),
    (.marks 60 8 83 false,7368),
    (.marks 60 8 86 false,5501),
    (.marks 60 9 65 false,401),
    (.marks 60 9 68 false,182),
    (.marks 60 9 71 false,221),
    (.marks 60 9 74 false,101),
    (.marks 60 9 77 false,101),
    (.marks 60 9 80 false,5601),
    (.marks 60 9 83 false,4235),
    (.marks 60 10 60 false,1601),
    (.marks 60 10 62 false,830),
    (.marks 60 10 65 false,373),
    (.marks 60 10 68 false,201),
    (.marks 60 10 71 false,101),
    (.marks 60 10 74 false,301),
    (.marks 60 10 77 false,2111),
    (.marks 60 10 80 false,5401),
    (.marks 60 11 62 false,101),
    (.marks 60 11 65 false,101),
    (.marks 60 11 68 false,201),
    (.marks 60 11 71 false,101),
    (.marks 60 11 74 false,101),
    (.marks 60 11 77 false,5892),
    (.marks 60 12 62 false,2501),
    (.marks 60 12 65 false,301),
    (.marks 60 12 68 false,101),
    (.marks 60 12 71 false,201),
    (.marks 60 12 74 false,2294),
    (.marks 60 12 77 false,2301),
    (.marks 60 13 62 false,201),
    (.marks 60 13 68 false,201),
    (.marks 60 13 71 false,201),
    (.marks 60 13 74 false,3595),
    (.marks 60 14 62 false,2401),
    (.marks 60 14 65 false,301),
    (.marks 60 14 68 false,101),
    (.marks 60 14 71 false,201),
    (.marks 60 14 74 false,2716),
    (.marks 60 15 68 false,301),
    (.marks 60 15 71 false,1301),
    (.marks 60 15 74 false,901),
    (.marks 60 16 65 false,2601),
    (.marks 60 16 71 false,1813),
    (.marks 60 17 65 false,646),
    (.marks 60 17 68 false,301),
    (.marks 60 17 71 false,1223),
    (.marks 60 18 65 false,1941),
    (.marks 60 18 68 false,1554),
    (.marks 60 18 71 false,1010),
    (.marks 60 19 68 false,805),
    (.marks 60 19 71 false,1429),
    (.marks 60 20 71 false,1334),
    (.marks 60 21 65 false,117),
    (.marks 60 21 68 false,1128),
    (.marks 60 21 71 false,399),
    (.marks 60 22 65 false,2201),
    (.marks 60 22 68 false,2194),
    (.marks 60 23 68 false,1803),
    (.marks 60 24 68 false,26),
    (.overlap 60 29 11 49,8201),
    (.overlap 60 30 11 49,20401),
    (.overlap 61 30 14 48,66401),
    (.overlap 61 32 14 48,8901),
    (.overlap 62 32 17 47,29501),
    (.overlap 62 33 17 47,8001),
    (.overlap 63 33 20 46,21401),
    (.overlap 63 34 20 46,26001),
    (.overlap 64 34 23 45,2001),
    (.overlap 64 35 23 45,26801),
    (.overlap 65 36 28 42,27601),
    (.overlap 65 37 28 42,4001),
    (.overlap 65 38 28 42,23101),
    (.overlap 65 39 28 42,9501)]⟩,
   []⟩

private theorem source105From60 : Window source105.plan source105.extras 60 67 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From68 : Window source105.plan source105.extras 68 75 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From76 : Window source105.plan source105.extras 76 83 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From84 : Window source105.plan source105.extras 84 91 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From92 : Window source105.plan source105.extras 92 99 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From100 : Window source105.plan source105.extras 100 107 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From108 : Window source105.plan source105.extras 108 115 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From116 : Window source105.plan source105.extras 116 123 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From124 : Window source105.plan source105.extras 124 131 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From132 : Window source105.plan source105.extras 132 139 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From140 : Window source105.plan source105.extras 140 147 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From148 : Window source105.plan source105.extras 148 155 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From156 : Window source105.plan source105.extras 156 163 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From164 : Window source105.plan source105.extras 164 171 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From172 : Window source105.plan source105.extras 172 179 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From180 : Window source105.plan source105.extras 180 187 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From188 : Window source105.plan source105.extras 188 195 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source105From196 : Window source105.plan source105.extras 196 199 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source105_valid : source105.Valid := by
  change source105.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join (join source105From60 source105From68) (join source105From76 source105From84)) (join (join source105From92 source105From100) (join source105From108 (join source105From116 source105From124)))) (join (join (join source105From132 source105From140) (join source105From148 source105From156)) (join (join source105From164 source105From172) (join source105From180 (join source105From188 source105From196)))))

end JSP233.PopulationSources20258
