module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.Concentrated40000
open ConcentratedBands20258
set_option autoImplicit false

def run83_1 : Run :=
  ⟨40000,[43659],0,.marked ⟨83,282,37,24000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run83_1_valid : run83_1.Valid 83 90 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run83_2 : Run :=
  ⟨43660,[45508,46548],0,.marked ⟨83,304,40,28000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run83_2_valid : run83_2.Valid 83 90 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run83_3 : Run :=
  ⟨46549,[47512,48253,48825,49280,49640],65,.marked ⟨83,288,38,25000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run83_3_valid : run83_3.Valid 83 90 := by
  apply Run.validate (z:=2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def run83_4 : Run :=
  ⟨49641,[50101,50524,50916,51276,51612,51930,52229,52512,52785,53046,53297,53540,53776,54004,54230,54450,54672,54890,55104,55320,55533,55751,55968,56188,56408],70,.marked ⟨83,288,38,25000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run83_4_valid : run83_4.Valid 83 90 := by
  apply Run.validate (z:=9) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def run83_5 : Run :=
  ⟨56409,[56745,57112,57508,57940,58409,58924,59492,60124,60831,61628,62533,63574,64780,65171],75,.marked ⟨83,282,37,24000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run83_5_valid : run83_5.Valid 83 90 := by
  apply Run.validate (z:=5) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band83 : Band := ⟨83,90,[run83_1,run83_2,run83_3,run83_4,run83_5]⟩

theorem band83_valid : band83.Layout 40000 65171 ∧ ∀ r∈band83.runs,r.Valid band83.lower band83.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band83,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact run83_1_valid
  · exact run83_2_valid
  · exact run83_3_valid
  · exact run83_4_valid
  · exact run83_5_valid

end JSP233.Concentrated40000
