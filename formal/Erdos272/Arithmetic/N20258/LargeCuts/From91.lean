module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.LargeCuts20258
open ConcentratedBands20258
set_option autoImplicit false

def run91_1 : Run :=
  ⟨20258,[27765],0,.marked ⟨91,230,27,16000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run91_1_valid : run91_1.Valid 91 110 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run91_2 : Run :=
  ⟨27766,[37410,39999],0,.marked ⟨91,264,32,21000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run91_2_valid : run91_2.Valid 91 110 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def band91 : Band := ⟨91,110,[run91_1,run91_2]⟩

theorem band91_valid : band91.Layout 20258 39999 ∧ ∀ r∈band91.runs,r.Valid band91.lower band91.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band91,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact run91_1_valid
  · exact run91_2_valid

end JSP233.LargeCuts20258
