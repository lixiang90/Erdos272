module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.Concentrated40000
open ConcentratedBands20258
set_option autoImplicit false

def run77_1 : Run :=
  ⟨40000,[40401,40800,41184,41571,41956,42344,42741,43144,43560,43993,44452,44935,45451,46012,46620,47295,48047,48895,49863,50984,52300,53874,55792,58176,61204,65148,65171],70,.marked ⟨77,250,34,19000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run77_1_valid : run77_1.Valid 77 78 := by
  apply Run.validate (z:=9) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band77 : Band := ⟨77,78,[run77_1]⟩

theorem band77_valid : band77.Layout 40000 65171 ∧ ∀ r∈band77.runs,r.Valid band77.lower band77.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band77,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run77_1_valid

def run79_1 : Run :=
  ⟨40000,[40722,41288,41736,42097],65,.marked ⟨79,270,36,22000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run79_1_valid : run79_1.Valid 79 82 := by
  apply Run.validate (z:=2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def run79_2 : Run :=
  ⟨42098,[42576,43020,43428,43813,44176,44525,44856,45177,45494,45801,46101,46400,46698,46995],70,.marked ⟨79,270,36,22000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run79_2_valid : run79_2.Valid 79 82 := by
  apply Run.validate (z:=5) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def run79_3 : Run :=
  ⟨46996,[47456,47952,48496,49092,49751,50490,51320,52262,53348,54612,56104,57891,60064,62753,65171],75,.marked ⟨79,257,34,20000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run79_3_valid : run79_3.Valid 79 82 := by
  apply Run.validate (z:=5) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band79 : Band := ⟨79,82,[run79_1,run79_2,run79_3]⟩

theorem band79_valid : band79.Layout 40000 65171 ∧ ∀ r∈band79.runs,r.Valid band79.lower band79.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band79,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact run79_1_valid
  · exact run79_2_valid
  · exact run79_3_valid

end JSP233.Concentrated40000
