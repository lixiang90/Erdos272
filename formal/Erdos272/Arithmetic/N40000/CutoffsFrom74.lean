module

public import Erdos272.Global.N20258.ConcentratedBands20258

@[expose] public section
namespace JSP233.Concentrated40000
open ConcentratedBands20258
set_option autoImplicit false

def run74_1 : Run :=
  ⟨40000,[40310,40656,41045,41484,41988,42564,43232,44014,44936,46036,47364,48994,51024,53592,56904,61162],75,.marked ⟨74,230,31,16000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run74_1_valid : run74_1.Valid 74 74 := by
  apply Run.validate (z:=6) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band74 : Band := ⟨74,74,[run74_1]⟩

theorem band74_valid : band74.Layout 40000 65171 ∧ ∀ r∈band74.runs,r.Valid band74.lower band74.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band74,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run74_1_valid

def run75_1 : Run :=
  ⟨40000,[40376,40788,41240,41745,42305,42936,43654,44480,45438,46564,47904,49524,51516,54002,57171,61296,62832],75,.marked ⟨75,237,32,17000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run75_1_valid : run75_1.Valid 75 75 := by
  apply Run.validate (z:=6) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band75 : Band := ⟨75,75,[run75_1]⟩

theorem band75_valid : band75.Layout 40000 65171 ∧ ∀ r∈band75.runs,r.Valid band75.lower band75.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band75,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run75_1_valid

def run76_1 : Run :=
  ⟨40000,[40472,40952,41453,41974,42525,43116,43748,44440,45208,46068,47043,48168,49488,51063,52983,55368,58401,62353,64525],70,.marked ⟨76,244,33,18000⟩⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem run76_1_valid : run76_1.Valid 76 76 := by
  apply Run.validate (z:=7) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

def band76 : Band := ⟨76,76,[run76_1]⟩

theorem band76_valid : band76.Layout 40000 65171 ∧ ∀ r∈band76.runs,r.Valid band76.lower band76.upper := by
  refine ⟨by decide +kernel,?_⟩
  intro r hr
  simp only [band76,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl
  · exact run76_1_valid

end JSP233.Concentrated40000
