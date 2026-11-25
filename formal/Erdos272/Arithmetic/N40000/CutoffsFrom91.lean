module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.Concentrated40000
open ConcentratedBands20258
set_option autoImplicit false

def run91_1 : Run :=
  ⟨40000,[51120],0,.marked ⟨91,298,36,27000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run91_1_valid : run91_1.Valid 91 110 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run91_2 : Run :=
  ⟨51121,[58466],0,.marked ⟨91,320,40,31000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run91_2_valid : run91_2.Valid 91 110 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run91_3 : Run :=
  ⟨58467,[62658,64695,65171],0,.marked ⟨91,350,44,37000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run91_3_valid : run91_3.Valid 91 110 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def band91 : Band := ⟨91,110,[run91_1,run91_2,run91_3]⟩

theorem band91_valid : band91.Layout 40000 65171 ∧ ∀ r∈band91.runs,r.Valid band91.lower band91.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band91,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact run91_1_valid
  · exact run91_2_valid
  · exact run91_3_valid

def run111_1 : Run :=
  ⟨40000,[54256,64001],0,.marked ⟨111,325,35,32000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run111_1_valid : run111_1.Valid 111 449 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def run111_2 : Run :=
  ⟨64002,[65171],0,.marked ⟨111,330,35,33000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run111_2_valid : run111_2.Valid 111 449 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def band111 : Band := ⟨111,449,[run111_1,run111_2]⟩

theorem band111_valid : band111.Layout 40000 65171 ∧ ∀ r∈band111.runs,r.Valid band111.lower band111.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band111,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact run111_1_valid
  · exact run111_2_valid

def run450_1 : Run :=
  ⟨40000,[40770,41555,42359,43176,44012,44864,45731,46619,47520,48443,49381,50339,51316,52313,53328,54366,55425,56505,57605,58727,59872,61040,62231,63444,64680,65171],80,.uniform 450⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run450_1_valid : run450_1.Valid 450 5500 := by
  apply Run.validate (z:=9) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band450 : Band := ⟨450,5500,[run450_1]⟩

theorem band450_valid : band450.Layout 40000 65171 ∧ ∀ r∈band450.runs,r.Valid band450.lower band450.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band450,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run450_1_valid

end JSP233.Concentrated40000
