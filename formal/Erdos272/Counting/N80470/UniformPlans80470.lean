module

public import Erdos272.Arithmetic.N84364.UniformNumeric84364

@[expose] public section

namespace JSP233.UniformPlans80470
open UniformNumeric84364
set_option autoImplicit false

def plan (k : ℕ) : Plan :=
  match k with
  | 0 => ⟨86,2186⟩
  | 1 => ⟨356,38220⟩
  | 2 => ⟨399,48000⟩
  | 3 => ⟨425,54522⟩
  | 4 => ⟨219,14360⟩
  | _ => ⟨0,0⟩

end JSP233.UniformPlans80470
