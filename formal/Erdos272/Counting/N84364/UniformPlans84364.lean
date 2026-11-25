module

public import Erdos272.Arithmetic.N84364.UniformNumericPilot84364

@[expose] public section

namespace JSP233.UniformPlans84364
open UniformNumeric84364
set_option autoImplicit false

def plan (k : ℕ) : Plan :=
  match k with
  | 0 => UniformNumericPilot84364.plan0
  | 1 => UniformNumericPilot84364.plan1
  | 2 => UniformNumericPilot84364.plan3
  | 3 => ⟨223,14984⟩
  | 4 => ⟨243,17810⟩
  | 5 => ⟨273,22442⟩
  | 6 => ⟨284,24304⟩
  | 7 => ⟨295,26106⟩
  | 8 => ⟨305,27899⟩
  | 9 => ⟨308,28545⟩
  | 10 => ⟨319,30758⟩
  | 11 => ⟨363,39616⟩
  | 12 => ⟨374,42260⟩
  | 13 => ⟨386,44800⟩
  | 14 => ⟨392,46400⟩
  | 15 => ⟨402,48766⟩
  | 16 => ⟨407,50088⟩
  | 17 => ⟨418,52556⟩
  | 18 => ⟨426,54720⟩
  | 19 => ⟨433,56546⟩
  | 20 => ⟨439,57994⟩
  | 21 => ⟨443,59288⟩
  | 22 => ⟨225,15176⟩
  | _ => ⟨0,0⟩

end JSP233.UniformPlans84364
