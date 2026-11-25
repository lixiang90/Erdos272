module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.Concentrated40000
open ConcentratedBands20258
set_option autoImplicit false

def run60_1 : Run :=
  ⟨40000,[41205,42858,44277],80,.marked ⟨60,152,23,7000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run60_1_valid : run60_1.Valid 60 63 := by
  apply Run.validate (z:=1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i ; decide +kernel

def band60 : Band := ⟨60,63,[run60_1]⟩

theorem band60_valid : band60.Layout 40000 65171 ∧ ∀ r∈band60.runs,r.Valid band60.lower band60.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band60,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run60_1_valid

def run64_1 : Run :=
  ⟨40000,[40535,41236,42162,43395,45037,47250,48611],80,.marked ⟨64,172,25,9000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run64_1_valid : run64_1.Valid 64 66 := by
  apply Run.validate (z:=3) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band64 : Band := ⟨64,66,[run64_1]⟩

theorem band64_valid : band64.Layout 40000 65171 ∧ ∀ r∈band64.runs,r.Valid band64.lower band64.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band64,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run64_1_valid

def run67_1 : Run :=
  ⟨40000,[40310,40704,41204,41843,42660,43713,45078,46863,49218,51613],80,.marked ⟨67,191,27,11000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run67_1_valid : run67_1.Valid 67 68 := by
  apply Run.validate (z:=4) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band67 : Band := ⟨67,68,[run67_1]⟩

theorem band67_valid : band67.Layout 40000 65171 ∧ ∀ r∈band67.runs,r.Valid band67.lower band67.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band67,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run67_1_valid

def run69_1 : Run :=
  ⟨40000,[40410,40928,41580,42406,43464,44827,46608,48960,52113,53148],75,.marked ⟨69,199,28,12000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run69_1_valid : run69_1.Valid 69 69 := by
  apply Run.validate (z:=4) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band69 : Band := ⟨69,69,[run69_1]⟩

theorem band69_valid : band69.Layout 40000 65171 ∧ ∀ r∈band69.runs,r.Valid band69.lower band69.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band69,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run69_1_valid

end JSP233.Concentrated40000
