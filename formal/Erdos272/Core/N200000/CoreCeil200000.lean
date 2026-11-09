module

public import Erdos272.Foundation.ProofTactics

@[expose] public section

namespace JSP233.CoreCeil200000
theorem ceil_count {V B : ℕ} (hV : 0 < V) (hB : 0 < B) : (V - 1) / B + 1 = (V + B - 1) / B := by
  rw [show V + B - 1 = (V - 1) + B by omega, Nat.add_div_right _ hB]

#print axioms ceil_count
end JSP233.CoreCeil200000
