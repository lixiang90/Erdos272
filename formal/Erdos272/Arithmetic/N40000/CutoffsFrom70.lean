module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.Concentrated40000
open ConcentratedBands20258
set_option autoImplicit false

def run70_1 : Run :=
  ⟨40000,[40296,40657,41100,41648,42330,43182,44259,45630,47397,49707,52773,54706],75,.marked ⟨70,208,29,13000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run70_1_valid : run70_1.Valid 70 70 := by
  apply Run.validate (z:=4) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band70 : Band := ⟨70,70,[run70_1]⟩

theorem band70_valid : band70.Layout 40000 65171 ∧ ∀ r∈band70.runs,r.Valid band70.lower band70.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band70,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run70_1_valid

def run71_1 : Run :=
  ⟨40000,[40220,40482,40795,41172,41624,42176,42849,43677,44710,46004,47646,49764,52530,56211,56286],75,.marked ⟨71,216,30,14000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run71_1_valid : run71_1.Valid 71 71 := by
  apply Run.validate (z:=5) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band71 : Band := ⟨71,71,[run71_1]⟩

theorem band71_valid : band71.Layout 40000 65171 ∧ ∀ r∈band71.runs,r.Valid band71.lower band71.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band71,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run71_1_valid

def run72_1 : Run :=
  ⟨40000,[40161,40348,40570,40826,41127,41482,41902,42404,43004,43728,44608,45693,47040,48735,50900,53710,57420,57889],75,.marked ⟨72,223,31,15000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run72_1_valid : run72_1.Valid 72 72 := by
  apply Run.validate (z:=6) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band72 : Band := ⟨72,72,[run72_1]⟩

theorem band72_valid : band72.Layout 40000 65171 ∧ ∀ r∈band72.runs,r.Valid band72.lower band72.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band72,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run72_1_valid

def run73_1 : Run :=
  ⟨40000,[40160,40347,40560,40806,41089,41420,41808,42264,42800,43440,44208,45138,46275,47680,49443,51687,54594,58422,59514],75,.marked ⟨73,223,31,15000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run73_1_valid : run73_1.Valid 73 73 := by
  apply Run.validate (z:=7) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band73 : Band := ⟨73,73,[run73_1]⟩

theorem band73_valid : band73.Layout 40000 65171 ∧ ∀ r∈band73.runs,r.Valid band73.lower band73.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band73,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run73_1_valid

end JSP233.Concentrated40000
