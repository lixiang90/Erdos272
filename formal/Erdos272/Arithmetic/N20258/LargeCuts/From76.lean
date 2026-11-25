module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.LargeCuts20258
open ConcentratedBands20258
set_option autoImplicit false

def run76_1 : Run :=
  ⟨20258,[25584,29536],0,.marked ⟨76,223,30,15000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run76_1_valid : run76_1.Valid 76 77 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run76_2 : Run :=
  ⟨29537,[32045,32916],0,.marked ⟨76,244,33,18000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run76_2_valid : run76_2.Valid 76 77 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run76_3 : Run :=
  ⟨32917,[33856,34568,35118,35550,35890,36162],65,.marked ⟨76,244,33,18000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run76_3_valid : run76_3.Valid 76 77 := by
  apply Run.validate (z:=2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def run76_4 : Run :=
  ⟨36163,[36496,36804,37087,37355,37602,37835,38055,38268,38472,38664,38850,39033,39210,39384,39554,39720,39888,39999],70,.marked ⟨76,244,33,18000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run76_4_valid : run76_4.Valid 76 77 := by
  apply Run.validate (z:=6) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band76 : Band := ⟨76,77,[run76_1,run76_2,run76_3,run76_4]⟩

theorem band76_valid : band76.Layout 20258 39999 ∧ ∀ r∈band76.runs,r.Valid band76.lower band76.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band76,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact run76_1_valid
  · exact run76_2_valid
  · exact run76_3_valid
  · exact run76_4_valid

end JSP233.LargeCuts20258
