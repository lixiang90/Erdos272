module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.LargeCuts20258
open ConcentratedBands20258
set_option autoImplicit false

def run78_1 : Run :=
  ⟨20258,[26049,30001],0,.marked ⟨78,223,29,15000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run78_1_valid : run78_1.Valid 78 80 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run78_2 : Run :=
  ⟨30002,[33930],0,.marked ⟨78,244,32,18000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run78_2_valid : run78_2.Valid 78 80 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run78_3 : Run :=
  ⟨33931,[35740,36796,37416],60,.marked ⟨78,257,35,20000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run78_3_valid : run78_3.Valid 78 80 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run78_4 : Run :=
  ⟨37417,[38141,38704,39152,39515,39809,39999],65,.marked ⟨78,257,35,20000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run78_4_valid : run78_4.Valid 78 80 := by
  apply Run.validate (z:=2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band78 : Band := ⟨78,80,[run78_1,run78_2,run78_3,run78_4]⟩

theorem band78_valid : band78.Layout 20258 39999 ∧ ∀ r∈band78.runs,r.Valid band78.lower band78.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band78,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact run78_1_valid
  · exact run78_2_valid
  · exact run78_3_valid
  · exact run78_4_valid

end JSP233.LargeCuts20258
