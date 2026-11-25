module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.LargeCuts20258
open ConcentratedBands20258
set_option autoImplicit false

def run111_1 : Run :=
  ⟨20258,[26659],0,.marked ⟨111,230,24,16000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run111_1_valid : run111_1.Valid 111 449 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run111_2 : Run :=
  ⟨26660,[35724,39999],0,.marked ⟨111,270,28,22000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run111_2_valid : run111_2.Valid 111 449 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def band111 : Band := ⟨111,449,[run111_1,run111_2]⟩

theorem band111_valid : band111.Layout 20258 39999 ∧ ∀ r∈band111.runs,r.Valid band111.lower band111.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band111,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact run111_1_valid
  · exact run111_2_valid

end JSP233.LargeCuts20258
