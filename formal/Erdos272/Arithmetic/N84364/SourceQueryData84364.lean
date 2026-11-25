module

public import Erdos272.Resources.N109474.CorrelatedSource109474

@[expose] public section

namespace JSP233.SourceQueryData84364
open CorrelatedSource109474
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def queries : List Plan := [
  ⟨154, 5, 30758, 27⟩,
  ⟨132, 8, 33842, 32⟩,
  ⟨154, 6, 36984, 28⟩,
  ⟨132, 11, 44800, 37⟩,
  ⟨133, 13, 51138, 40⟩]

def query (i : ℕ) : Plan := (queries[i]?).getD ⟨0,0,0,0⟩

theorem checked0 : (List.range 5).all (fun j => decide (Conditions (query (0+j)))) = true := by decide +kernel
#print axioms checked0

theorem piece0 {i : ℕ} (hlo : 0 ≤ i) (hhi : i < 5) : Conditions (query i) := by
  have hm : i-0 ∈ List.range 5 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked0 (i-0) hm)
  have he : 0+(i-0) = i := by omega
  simpa only [he] using hc
#print axioms piece0

theorem conditions {i : ℕ} (hi : i < 5) : Conditions (query i) := by
  exact piece0 (by omega) hi
#print axioms conditions
end
end JSP233.SourceQueryData84364
