module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.LargeCuts20258
open ConcentratedBands20258
set_option autoImplicit false

def run85_1 : Run :=
  ⟨20258,[27190],0,.marked ⟨85,230,28,16000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run85_1_valid : run85_1.Valid 85 90 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run85_2 : Run :=
  ⟨27191,[35550,39999],0,.marked ⟨85,257,32,20000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run85_2_valid : run85_2.Valid 85 90 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def band85 : Band := ⟨85,90,[run85_1,run85_2]⟩

theorem band85_valid : band85.Layout 20258 39999 ∧ ∀ r∈band85.runs,r.Valid band85.lower band85.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band85,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact run85_1_valid
  · exact run85_2_valid

end JSP233.LargeCuts20258
