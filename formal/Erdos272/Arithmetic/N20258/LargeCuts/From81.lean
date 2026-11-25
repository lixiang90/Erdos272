module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.LargeCuts20258
open ConcentratedBands20258
set_option autoImplicit false

def run81_1 : Run :=
  ⟨20258,[26592],0,.marked ⟨81,223,28,15000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run81_1_valid : run81_1.Valid 81 84 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run81_2 : Run :=
  ⟨26593,[33525,37759],0,.marked ⟨81,250,32,19000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run81_2_valid : run81_2.Valid 81 84 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run81_3 : Run :=
  ⟨37760,[39999],0,.marked ⟨81,264,34,21000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run81_3_valid : run81_3.Valid 81 84 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def band81 : Band := ⟨81,84,[run81_1,run81_2,run81_3]⟩

theorem band81_valid : band81.Layout 20258 39999 ∧ ∀ r∈band81.runs,r.Valid band81.lower band81.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band81,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact run81_1_valid
  · exact run81_2_valid
  · exact run81_3_valid

end JSP233.LargeCuts20258
