module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.LargeCuts20258
open ConcentratedBands20258
set_option autoImplicit false

def run450_1 : Run :=
  ⟨20258,[20638,21023,21419,21822,22233,22652,23077,23512,23955,24407,24868,25340,25821,26312,26810,27320,27839,28368,28907,29459,30023,30599,31185,31780,32387,33008,33640,34283,34943,35615,36299,36995,37705,38431,39170,39924,39999],80,.uniform 450⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run450_1_valid : run450_1.Valid 450 3400 := by
  apply Run.validate (z:=13) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band450 : Band := ⟨450,3400,[run450_1]⟩

theorem band450_valid : band450.Layout 20258 39999 ∧ ∀ r∈band450.runs,r.Valid band450.lower band450.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band450,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run450_1_valid

end JSP233.LargeCuts20258
