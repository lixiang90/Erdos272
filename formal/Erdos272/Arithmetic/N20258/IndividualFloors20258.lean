module

public import Erdos272.Arithmetic.N20258.Floors.From40
public import Erdos272.Arithmetic.N20258.Floors.From48
public import Erdos272.Arithmetic.N20258.Floors.From56
public import Erdos272.Arithmetic.N20258.Floors.From64
public import Erdos272.Arithmetic.N20258.Floors.From72
public import Erdos272.Arithmetic.N20258.Floors.From80
public import Erdos272.Arithmetic.N20258.Floors.From88
public import Erdos272.Arithmetic.N20258.Floors.From96
public import Erdos272.Arithmetic.N20258.Floors.From104
public import Erdos272.Arithmetic.N20258.Floors.From112
public import Erdos272.Arithmetic.N20258.Floors.From120
public import Erdos272.Arithmetic.N20258.Floors.From128
public import Erdos272.Arithmetic.N20258.Floors.From136
public import Erdos272.Arithmetic.N20258.Floors.From144
public import Erdos272.Arithmetic.N20258.Floors.From152
public import Erdos272.Arithmetic.N20258.Floors.From160
public import Erdos272.Arithmetic.N20258.Floors.From168
public import Erdos272.Arithmetic.N20258.Floors.From176
public import Erdos272.Arithmetic.N20258.Floors.From184
public import Erdos272.Arithmetic.N20258.Floors.From192
public import Erdos272.Arithmetic.N20258.Floors.From200
public import Erdos272.Arithmetic.N20258.Floors.From208
public import Erdos272.Arithmetic.N20258.Floors.From216
public import Erdos272.Arithmetic.N20258.Floors.From224
public import Erdos272.Arithmetic.N20258.Floors.From232
public import Erdos272.Arithmetic.N20258.Floors.From240
public import Erdos272.Arithmetic.N20258.Floors.From248

@[expose] public section
namespace JSP233.IndividualFloors20258
open PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def prices : Floor :=
  (select 144 (select 88 (select 64 (select 48 from40 (select 56 from48 from56)) (select 72 from64 (select 80 from72 from80))) (select 112 (select 96 from88 (select 104 from96 from104)) (select 128 (select 120 from112 from120) (select 136 from128 from136)))) (select 200 (select 168 (select 152 from144 (select 160 from152 from160)) (select 184 (select 176 from168 from176) (select 192 from184 from192))) (select 224 (select 208 from200 (select 216 from208 from216)) (select 240 (select 232 from224 from232) (select 248 from240 from248)))))

end JSP233.IndividualFloors20258
